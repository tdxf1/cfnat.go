package main

import (
	"bufio"
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net"
	"net/http"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

const (
	timeout     = 1 * time.Second // 超时时间
	maxDuration = 2 * time.Second // 最大持续时间

	baiduFakeHost  = "sptest.baidu.com"
	baiduUserAgent = "okhttp/3.11.0 Dalvik/2.1.0 (Linux; Build/RKQ1.200826.002) baiduboxapp/11.0.5.12 (Baidu; P1 11)"
	baiduAuthToken = "482857715"

	carrierMobile  = "mobile"
	carrierTelecom = "telecom"
	carrierUnicom  = "unicom"

	// 代理节点隔离参数：连续失败达到阈值后临时剔除该节点，隔离时长指数退避、有上限，
	// 成功一次立即解除。阈值和退避都偏激进，与 forwardFailCount>=2 的整体切换风格一致。
	quarantineThreshold = 3                 // 连续失败 3 次即隔离
	quarantineBase      = 10 * time.Second  // 隔离基础时长
	quarantineMax       = 120 * time.Second // 隔离时长上限
)

var (
	activeConnections  int32 // 用于跟踪活跃连接的数量
	validIPClientCache sync.Map

	randomMu        sync.Mutex
	randomGenerator = rand.New(rand.NewSource(time.Now().UnixNano()))

	// forwardFailCount 记录业务转发连续失败次数，供 statusCheck 提前触发 IP 切换。
	forwardFailCount int32
)

var carrierDisplayNames = map[string]string{
	carrierMobile:  "中国移动",
	carrierTelecom: "中国电信",
	carrierUnicom:  "中国联通",
}

var defaultCarrierResolvers = map[string][]string{
	carrierMobile:  {"221.131.143.69:53", "112.4.0.55:53", "211.138.180.2:53"},
	carrierTelecom: {"202.96.209.133:53", "202.96.128.86:53", "202.103.24.68:53"},
	carrierUnicom:  {"202.106.0.20:53", "210.21.196.6:53", "221.5.88.88:53"},
}

var defaultBaiduResolvers = []string{
	"223.5.5.5:53",
	"223.6.6.6:53",
	"119.29.29.29:53",
	"180.76.76.76:53",
	"114.114.114.114:53",
	"1.1.1.1:53",
	"8.8.8.8:53",
}

// IPManager 用于安全管理 IP 地址状态
type IPManager struct {
	mu           sync.RWMutex
	currentIP    string
	ipAddresses  []string
	currentIndex int
}

func NewIPManager() *IPManager {
	return &IPManager{}
}

func (m *IPManager) SetIPAddresses(ips []string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.ipAddresses = ips
	m.currentIndex = 0
}

func (m *IPManager) GetCurrentIP() string {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.currentIP
}

// SetCurrentIP 设置当前 IP 的同时同步 currentIndex，
// 保证 switchToNextValidIP 的遍历起点与实际选中的 IP 位置一致。
func (m *IPManager) SetCurrentIP(ip string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.currentIP = ip
	for i, addr := range m.ipAddresses {
		if addr == ip {
			m.currentIndex = i
			break
		}
	}
}

func (m *IPManager) GetIPAddresses() []string {
	m.mu.RLock()
	defer m.mu.RUnlock()
	return m.ipAddresses
}

func (m *IPManager) Clear() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.ipAddresses = []string{}
	m.currentIP = ""
	m.currentIndex = 0
}

// switchToNextValidIP 以 currentIndex 为起点环形遍历一整圈，
// 保证列表中所有 IP 都有机会被尝试一次，而不是只检查到列表末尾。
//
// 注意：网络探测（checkValidIP）单次耗时可达数百毫秒到数秒，且需要逐个尝试整份列表，
// 因此先在持锁状态下拍摄一份 (ipAddresses, currentIndex, currentIP) 快照后立即解锁，
// 所有探测都在不持锁的情况下进行；只有最终确定新 IP 时才重新加锁写回，
// 避免长时间独占写锁阻塞 GetCurrentIP/GetIPAddresses 等只读调用方
// （例如 Accept 循环中每个新连接都要读取 currentIP）。
func (m *IPManager) switchToNextValidIP(useTLS bool, port int, domain string, code int, proxyPool *BaiduProxyPool) bool {
	m.mu.RLock()
	n := len(m.ipAddresses)
	if n == 0 {
		m.mu.RUnlock()
		return false
	}
	ips := make([]string, n)
	copy(ips, m.ipAddresses)
	startIndex := m.currentIndex
	currentIP := m.currentIP
	m.mu.RUnlock()

	for offset := 1; offset <= n; offset++ {
		i := (startIndex + offset) % n
		ip := ips[i]
		// 跳过当前 IP
		if ip == currentIP {
			continue
		}
		if checkValidIP(ip, port, useTLS, domain, code, proxyPool) {
			m.mu.Lock()
			m.currentIP = ip
			// 重新在最新的 ipAddresses 中定位索引，防止探测期间列表被并发替换（如 SetIPAddresses/Clear）
			m.currentIndex = i
			for idx, addr := range m.ipAddresses {
				if addr == ip {
					m.currentIndex = idx
					break
				}
			}
			log.Printf("切换到新的有效 IP: %s 更新 IP 索引: %d", m.currentIP, m.currentIndex)
			m.mu.Unlock()
			return true
		}
	}
	log.Println("所有 IP 都已检查过，程序将退出")
	return false
}

type result struct {
	ip          string        // IP地址
	dataCenter  string        // 数据中心
	region      string        // 地区
	city        string        // 城市
	latency     string        // 延迟
	tcpDuration time.Duration // TCP请求延迟
}

type location struct {
	Iata   string  `json:"iata"`
	Lat    float64 `json:"lat"`
	Lon    float64 `json:"lon"`
	Cca2   string  `json:"cca2"`
	Region string  `json:"region"`
	City   string  `json:"city"`
}

type carrierListenSpec struct {
	carrier string
	addr    string
}

// proxyEndpoint 的 quarantineUntil 存 UnixNano 时间戳，0 或已过期表示未被隔离；
// 全部用原子操作读写，不额外加锁。
type proxyEndpoint struct {
	addr            string
	active          int32
	ewmaNanos       int64
	failures        int32
	quarantineUntil int64
}

type BaiduProxyPool struct {
	name      string
	endpoints []*proxyEndpoint
}

func NewBaiduProxyPool(name string, addrs []string) *BaiduProxyPool {
	pool := &BaiduProxyPool{name: name}
	for _, addr := range dedupeStrings(addrs) {
		pool.endpoints = append(pool.endpoints, &proxyEndpoint{
			addr:      addr,
			ewmaNanos: int64(timeout),
		})
	}
	return pool
}

func (p *BaiduProxyPool) CacheKey() string {
	if p == nil {
		return "direct"
	}
	addrs := make([]string, 0, len(p.endpoints))
	for _, endpoint := range p.endpoints {
		addrs = append(addrs, endpoint.addr)
	}
	sort.Strings(addrs)
	return p.name + "|" + strings.Join(addrs, ",")
}

func (p *BaiduProxyPool) Len() int {
	if p == nil {
		return 0
	}
	return len(p.endpoints)
}

func (p *BaiduProxyPool) Addresses() []string {
	if p == nil {
		return nil
	}
	addrs := make([]string, 0, len(p.endpoints))
	for _, endpoint := range p.endpoints {
		addrs = append(addrs, endpoint.addr)
	}
	return addrs
}

// pick 优先在未隔离节点中做 power-of-two choices；
// 若全部节点都在隔离期（如网络大面积故障），退化为在全量节点中选择，避免池子彻底不可用。
func (p *BaiduProxyPool) pick() *proxyEndpoint {
	if p == nil || len(p.endpoints) == 0 {
		return nil
	}

	pool := p.endpoints
	var available []*proxyEndpoint
	for _, e := range p.endpoints {
		if !e.quarantined() {
			available = append(available, e)
		}
	}
	if len(available) > 0 {
		pool = available
	}

	if len(pool) == 1 {
		return pool[0]
	}
	a := pool[nextRandomIntn(len(pool))]
	b := pool[nextRandomIntn(len(pool))]
	for b == a && len(pool) > 1 {
		b = pool[nextRandomIntn(len(pool))]
	}
	if b.scoreNanos() < a.scoreNanos() {
		return b
	}
	return a
}

func (p *BaiduProxyPool) Dial(ctx context.Context, targetAddr string, dialTimeout time.Duration) (net.Conn, error) {
	if p == nil || len(p.endpoints) == 0 {
		return nil, errors.New("百度代理池为空")
	}
	attempts := len(p.endpoints)
	if attempts > 3 {
		attempts = 3
	}
	var lastErr error
	for i := 0; i < attempts; i++ {
		endpoint := p.pick()
		if endpoint == nil {
			return nil, errors.New("百度代理池没有可用节点")
		}
		atomic.AddInt32(&endpoint.active, 1)
		start := time.Now()
		conn, err := dialBaiduTunnelViaNode(ctx, endpoint.addr, targetAddr, dialTimeout)
		elapsed := time.Since(start)
		if err != nil {
			atomic.AddInt32(&endpoint.active, -1)
			endpoint.recordFailure(elapsed)
			lastErr = fmt.Errorf("%s: %w", endpoint.addr, err)
			continue
		}
		endpoint.recordSuccess(elapsed)
		return &trackedProxyConn{Conn: conn, endpoint: endpoint}, nil
	}
	return nil, lastErr
}

func (e *proxyEndpoint) scoreNanos() int64 {
	ewma := atomic.LoadInt64(&e.ewmaNanos)
	if ewma <= 0 {
		ewma = int64(timeout)
	}
	active := int64(atomic.LoadInt32(&e.active))
	failures := int64(atomic.LoadInt32(&e.failures))
	return ewma + active*int64(50*time.Millisecond) + failures*int64(300*time.Millisecond)
}

// recordSuccess 记录一次成功，并立即解除隔离。
func (e *proxyEndpoint) recordSuccess(elapsed time.Duration) {
	updateEWMA(&e.ewmaNanos, elapsed)
	decrementIfPositiveInt32(&e.failures)
	atomic.StoreInt64(&e.quarantineUntil, 0)
}

// recordFailure 记录一次失败，连续失败达到阈值后进入隔离期（指数退避、有上限）。
func (e *proxyEndpoint) recordFailure(elapsed time.Duration) {
	if elapsed > 0 {
		updateEWMA(&e.ewmaNanos, elapsed)
	}
	f := atomic.AddInt32(&e.failures, 1)
	if f >= quarantineThreshold {
		shift := f - quarantineThreshold
		if shift > 10 { // 防止移位过大溢出，10次后维持在上限
			shift = 10
		}
		backoff := quarantineBase * time.Duration(int64(1)<<uint(shift))
		if backoff > quarantineMax || backoff <= 0 {
			backoff = quarantineMax
		}
		until := time.Now().Add(backoff).UnixNano()
		atomic.StoreInt64(&e.quarantineUntil, until)
		log.Printf("百度代理节点 %s 连续失败 %d 次，隔离 %s", e.addr, f, backoff)
	}
}

// quarantined 判断节点当前是否处于隔离期
func (e *proxyEndpoint) quarantined() bool {
	until := atomic.LoadInt64(&e.quarantineUntil)
	return until != 0 && time.Now().UnixNano() < until
}

type trackedProxyConn struct {
	net.Conn
	endpoint *proxyEndpoint
	once     sync.Once
}

func (c *trackedProxyConn) Close() error {
	err := c.Conn.Close()
	c.once.Do(func() {
		atomic.AddInt32(&c.endpoint.active, -1)
	})
	return err
}

type targetEndpoint struct {
	ip        string
	addr      string
	active    int32
	ewmaNanos int64
	failures  int32
}

type TargetPool struct {
	name      string
	endpoints []*targetEndpoint
}

func NewTargetPool(name string, results []result, port int) *TargetPool {
	pool := &TargetPool{name: name}
	for _, r := range results {
		pool.endpoints = append(pool.endpoints, &targetEndpoint{
			ip:        r.ip,
			addr:      net.JoinHostPort(r.ip, strconv.Itoa(port)),
			ewmaNanos: int64(r.tcpDuration),
		})
	}
	return pool
}

func (p *TargetPool) Len() int {
	if p == nil {
		return 0
	}
	return len(p.endpoints)
}

func (p *TargetPool) pick() *targetEndpoint {
	if p == nil || len(p.endpoints) == 0 {
		return nil
	}
	if len(p.endpoints) == 1 {
		return p.endpoints[0]
	}
	a := p.endpoints[nextRandomIntn(len(p.endpoints))]
	b := p.endpoints[nextRandomIntn(len(p.endpoints))]
	for b == a && len(p.endpoints) > 1 {
		b = p.endpoints[nextRandomIntn(len(p.endpoints))]
	}
	if b.scoreNanos() < a.scoreNanos() {
		return b
	}
	return a
}

func (p *TargetPool) PickTargets(maxAttempts int) []*targetEndpoint {
	if p == nil || len(p.endpoints) == 0 {
		return nil
	}
	if maxAttempts <= 0 || maxAttempts > len(p.endpoints) {
		maxAttempts = len(p.endpoints)
	}
	targets := make([]*targetEndpoint, 0, maxAttempts)
	seen := make(map[*targetEndpoint]struct{}, maxAttempts)
	for len(targets) < maxAttempts {
		target := p.pick()
		if target == nil {
			break
		}
		if _, ok := seen[target]; ok {
			if len(seen) == len(p.endpoints) {
				break
			}
			continue
		}
		seen[target] = struct{}{}
		targets = append(targets, target)
	}
	return targets
}

func (e *targetEndpoint) scoreNanos() int64 {
	ewma := atomic.LoadInt64(&e.ewmaNanos)
	if ewma <= 0 {
		ewma = int64(timeout)
	}
	active := int64(atomic.LoadInt32(&e.active))
	failures := int64(atomic.LoadInt32(&e.failures))
	return ewma + active*int64(50*time.Millisecond) + failures*int64(300*time.Millisecond)
}

func (e *targetEndpoint) recordSuccess(elapsed time.Duration) {
	updateEWMA(&e.ewmaNanos, elapsed)
	decrementIfPositiveInt32(&e.failures)
}

func (e *targetEndpoint) recordFailure(elapsed time.Duration) {
	if elapsed > 0 {
		updateEWMA(&e.ewmaNanos, elapsed)
	}
	atomic.AddInt32(&e.failures, 1)
}

// decrementIfPositiveInt32 原子地执行"仅当当前值大于0时才减1"，
// 通过 CAS 循环把读取与写入合并为一个整体操作，避免多个 goroutine
// 并发调用时出现先读后写的竞态（读到 >0 后各自减 1，导致计数被过度递减甚至变为负数）。
func decrementIfPositiveInt32(dst *int32) {
	for {
		old := atomic.LoadInt32(dst)
		if old <= 0 {
			return
		}
		if atomic.CompareAndSwapInt32(dst, old, old-1) {
			return
		}
	}
}

func updateEWMA(dst *int64, sample time.Duration) {
	if sample <= 0 {
		return
	}
	sampleNanos := int64(sample)
	for {
		old := atomic.LoadInt64(dst)
		next := sampleNanos
		if old > 0 {
			next = (old*7 + sampleNanos) / 8
		}
		if atomic.CompareAndSwapInt64(dst, old, next) {
			return
		}
	}
}

func main() {
	localAddr := flag.String("addr", "0.0.0.0:1234", "本地监听的 IP 和端口")
	code := flag.Int("code", 200, "HTTP/HTTPS 响应状态码")
	coloFilter := flag.String("colo", "", "筛选数据中心例如 HKG,SJC,LAX (多个数据中心用逗号隔开,留空则忽略匹配)")
	delay := flag.Int("delay", 300, "有效延迟（毫秒），超过此延迟将断开连接")
	domain := flag.String("domain", "cloudflaremirrors.com/debian", "响应状态码检查的域名地址")
	ipCount := flag.Int("ipnum", 20, "提取的有效IP数量")
	ipsType := flag.String("ips", "4", "指定生成IPv4还是IPv6地址 (4或6)")
	num := flag.Int("num", 5, "目标负载 IP 数量")
	port := flag.Int("port", 443, "转发的目标端口")
	random := flag.Bool("random", true, "是否随机生成IP，如果为false，则从CIDR中拆分出所有IP")
	maxThreads := flag.Int("task", 100, "并发请求最大协程数")
	useTLS := flag.Bool("tls", true, "是否为 TLS 端口")
	useBaiduProxy := flag.Bool("baidu-proxy", true, "是否启用固定百度前置代理")
	baiduDomain := flag.String("baidu-domain", "cloudnproxy.baidu.com", "百度前置代理域名")
	baiduPort := flag.Int("baidu-port", 443, "百度前置代理端口")
	baiduScanTarget := flag.String("baidu-scan-target", "myip.ipip.net:80", "扫描百度代理IP池时用于 CONNECT 的目标")
	baiduIPCount := flag.Int("baidu-ipnum", 12, "每个运营商保留的百度代理IP数量")
	carrierListens := flag.String("carrier-listens", "", "按运营商启动多个监听端口，例如 mobile=0.0.0.0:1234,telecom=0.0.0.0:1235,unicom=0.0.0.0:1236")
	carrierResolvers := flag.String("carrier-resolvers", "", "额外用于聚合解析百度代理域名的DNS，例如 mobile=1.1.1.1:53|2.2.2.2:53,telecom=...,unicom=...")
	flag.Parse()

	if *ipsType != "4" && *ipsType != "6" {
		log.Fatalf("无效的 -ips 参数: %q，请使用 '4' 或 '6'", *ipsType)
	}

	// -ips=6 目前有两个限制：百度代理节点均为 IPv4（无法为 IPv6 目标建代理隧道），
	// 且 IPv6 网段不支持逐个展开（-random=false）。都在启动时直接拒绝。
	if *ipsType == "6" {
		if *useBaiduProxy {
			log.Fatalf("-ips=6 不支持 -baidu-proxy=true：百度代理节点均为 IPv4，无法为 IPv6 目标建立隧道。请使用 -ips=4 或 -baidu-proxy=false")
		}
		if !*random {
			log.Fatalf("-ips=6 不支持 -random=false：IPv6 网段暂不支持逐个展开。请使用 -ips=4 或保持 -random=true")
		}
	}

	if *carrierListens != "" {
		specs, err := parseCarrierListens(*carrierListens)
		if err != nil {
			log.Fatalf("解析 -carrier-listens 失败: %v", err)
		}
		resolvers, err := parseCarrierResolvers(*carrierResolvers)
		if err != nil {
			log.Fatalf("解析 -carrier-resolvers 失败: %v", err)
		}
		if err := runCarrierMode(specs, resolvers, *baiduDomain, *baiduPort, *baiduScanTarget, *baiduIPCount, *code, *coloFilter, *delay, *domain, *ipCount, *ipsType, *num, *port, *random, *maxThreads, *useTLS, *useBaiduProxy); err != nil {
			log.Fatalf("运营商分池模式失败: %v", err)
		}
		return
	}

	// 创建 IP 管理器
	ipManager := NewIPManager()

	var defaultProxyPool *BaiduProxyPool
	if *useBaiduProxy {
		defaultProxyPool = buildDefaultBaiduPool(*baiduDomain, *baiduPort, *baiduScanTarget, *baiduIPCount, *maxThreads)
	}

	// 启动 TCP 监听
	listener, err := net.Listen("tcp", *localAddr)
	if err != nil {
		log.Fatalf("无法监听 %s: %v", *localAddr, err)
	}
	defer listener.Close()

	if defaultProxyPool != nil {
		log.Printf("百度前置代理已启用: %s", strings.Join(defaultProxyPool.Addresses(), ","))
	} else {
		log.Printf("百度前置代理已关闭，使用直连拨号")
	}

	log.Printf("正在监听 %s 并转发到 %d 个目标地址，有效延迟：%d ms", *localAddr, *num, *delay)

	for {
		startTime := time.Now()

		// 使用函数处理 locations.json，确保 defer 正确执行
		locations, err := loadLocations()
		if err != nil {
			log.Printf("加载位置信息失败: %v", err)
			time.Sleep(3 * time.Second)
			continue
		}

		locationMap := make(map[string]location)
		for _, loc := range locations {
			locationMap[loc.Iata] = loc
		}

		// 获取候选 IP 列表：与运营商分池模式共用同一套下载/缓存/解析逻辑（loadCandidateIPs），
		// 避免两处维护同样的下载文件、读本地缓存、随机取样代码。
		// -ips 参数的合法性已在启动时校验过，这里失败只可能是网络或磁盘的临时性错误，
		// 记录日志后重试，不让长期运行的进程因为一次偶发的下载失败而退出。
		ipList, err := loadCandidateIPs(*ipsType, *random)
		if err != nil {
			log.Printf("加载候选 IP 列表失败: %v", err)
			time.Sleep(3 * time.Second)
			continue
		}

		// 从生成的 IP 列表进行处理
		results := scanIPs(ipList, locationMap, *maxThreads, defaultProxyPool)
		if len(results) == 0 {
			fmt.Println("未发现有效IP")
			time.Sleep(3 * time.Second)
			continue
		}

		// 应用数据中心筛选
		if *coloFilter != "" {
			filters := strings.Split(*coloFilter, ",")
			var filteredResults []result
			for _, r := range results {
				for _, filter := range filters {
					if strings.EqualFold(r.dataCenter, filter) {
						filteredResults = append(filteredResults, r)
						break
					}
				}
			}
			results = filteredResults
		}

		// 按 TCP 延迟排序
		sort.Slice(results, func(i, j int) bool {
			return results[i].tcpDuration < results[j].tcpDuration
		})

		// 只显示指定数量的 IP
		if len(results) > *ipCount {
			results = results[:*ipCount]
		}

		fmt.Println("IP 地址 | 数据中心 | 地区 | 城市 | 延迟")
		for _, r := range results {
			fmt.Printf("%s | %s | %s | %s | %s\n", r.ip, r.dataCenter, r.region, r.city, r.latency)
		}

		fmt.Printf("成功提取 %d 个有效IP，耗时 %d秒\n", len(results), time.Since(startTime)/time.Second)

		// 设置 IP 地址列表
		var ips []string
		for _, r := range results {
			ips = append(ips, r.ip)
		}
		ipManager.SetIPAddresses(ips)

		// 选择一个有效 IP
		currentIP := selectValidIP(ipManager, *useTLS, *port, *domain, *code, defaultProxyPool)
		if currentIP == "" {
			log.Printf("没有有效的 IP 可用")
			// 与下方 <-done 之后的清理路径保持对称，避免残留上一批已作废的状态。
			ipManager.Clear()
			validIPClientCache = sync.Map{}
			atomic.StoreInt32(&forwardFailCount, 0)
			time.Sleep(3 * time.Second)
			continue
		}
		ipManager.SetCurrentIP(currentIP)

		// 创建用于控制 goroutine 退出的 context
		ctx, cancel := context.WithCancel(context.Background())

		// 用于状态检查完成的信号
		done := make(chan bool)

		var loopWG sync.WaitGroup
		loopWG.Add(2)

		// 启动状态检查线程
		go func() {
			defer loopWG.Done()
			statusCheck(ctx, *localAddr, *useTLS, *port, done, *domain, *code, time.Duration(*delay)*time.Millisecond, ipManager, defaultProxyPool)
		}()

		// 主循环，接收连接
		go func() {
			defer loopWG.Done()
			for {
				select {
				case <-ctx.Done():
					log.Println("连接接受 goroutine 收到退出信号")
					return
				default:
					// 设置接受连接的超时，以便能够检查 context
					if tcpListener, ok := listener.(*net.TCPListener); ok {
						tcpListener.SetDeadline(time.Now().Add(1 * time.Second))
					}
					conn, err := listener.Accept()
					if err != nil {
						if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
							continue
						}
						if opErr, ok := err.(*net.OpError); ok && opErr.Err.Error() == "use of closed network connection" {
							return
						}
						log.Printf("接受连接时发生错误: %v", err)
						continue
					}
					clientAddr := conn.RemoteAddr().String()
					atomic.AddInt32(&activeConnections, 1)
					log.Printf("客户端来源: %s 连接建立，当前活跃连接数: %d", clientAddr, atomic.LoadInt32(&activeConnections))
					currIP := ipManager.GetCurrentIP()
					go handleConnection(conn, generateTargets(currIP, *port, *num), time.Duration(*delay)*time.Millisecond, defaultProxyPool)
				}
			}
		}()

		<-done
		cancel() // 取消 context，通知所有 goroutine 退出
		loopWG.Wait()

		// 清空 IP 地址
		ipManager.Clear()
		validIPClientCache = sync.Map{}
		atomic.StoreInt32(&forwardFailCount, 0)
		log.Println("所有候选 IP 均已失效，3 秒后重新扫描")
		time.Sleep(3 * time.Second)
	}
}

func runCarrierMode(specs []carrierListenSpec, resolvers map[string][]string, baiduDomain string, baiduPort int, baiduScanTarget string, baiduIPCount int, code int, coloFilter string, delayMS int, domain string, ipCount int, ipsType string, num int, port int, random bool, maxThreads int, useTLS bool, useBaiduProxy bool) error {
	locations, err := loadLocations()
	if err != nil {
		return fmt.Errorf("加载位置信息失败: %w", err)
	}
	locationMap := make(map[string]location)
	for _, loc := range locations {
		locationMap[loc.Iata] = loc
	}

	ipList, err := loadCandidateIPs(ipsType, random)
	if err != nil {
		return err
	}
	log.Printf("运营商分池模式启动，候选转发 IP 数量: %d", len(ipList))

	proxyPools := make(map[string]*BaiduProxyPool)
	if useBaiduProxy {
		if resolved := buildBaiduPoolsByCarrier(resolvers, baiduDomain, baiduPort, baiduScanTarget, baiduIPCount, maxThreads); resolved != nil {
			proxyPools = resolved
		}
		fallbackAddr := ensureHostPort(baiduDomain, baiduPort)
		for _, spec := range specs {
			if _, ok := proxyPools[spec.carrier]; !ok {
				// 该运营商没有匹配到任何百度代理节点：若创建一个空池，dialTarget 会始终把它当作
				// "启用了代理但无节点可用" 而直接失败，永远无法转发。这里回退为域名:端口这一个地址，
				// 与单端口模式 buildDefaultBaiduPool 的兜底策略保持一致，至少保留一次尝试的机会。
				log.Printf("%s 没有匹配到任何百度代理节点，回退使用域名地址: %s", carrierName(spec.carrier), fallbackAddr)
				proxyPools[spec.carrier] = NewBaiduProxyPool(spec.carrier, []string{fallbackAddr})
			}
		}
	} else {
		log.Printf("百度前置代理已关闭，运营商端口将使用直连拨号")
	}

	var listeners []net.Listener
	for _, spec := range specs {
		proxyPool := proxyPools[spec.carrier]
		results := scanCarrierTargets(spec.carrier, ipList, locationMap, maxThreads, proxyPool, coloFilter, ipCount)
		if len(results) == 0 {
			// 注意：carrier 模式启动后不会像单端口模式那样周期性重新扫描 IP，
			// TargetPool 一旦为空，PickTargets 会一直返回 nil，之后这个端口收到的每一个连接
			// 都会 100% 失败且永远不会自愈（唯一的恢复方式是重启进程）。与其起一个必然全部
			// 失败的监听，不如直接跳过该运营商并给出清晰告警，让问题在启动阶段就被发现。
			log.Printf("警告：%s 未扫描到任何可用转发目标，跳过该运营商监听（请检查 -colo 过滤条件是否过严，或稍后重启重试）", carrierName(spec.carrier))
			continue
		}
		targetPool := NewTargetPool(spec.carrier, results, port)

		listener, err := net.Listen("tcp", spec.addr)
		if err != nil {
			for _, l := range listeners {
				l.Close()
			}
			return fmt.Errorf("无法监听 %s(%s): %w", carrierName(spec.carrier), spec.addr, err)
		}
		listeners = append(listeners, listener)

		log.Printf("%s 监听 %s，百度代理节点 %d 个，转发目标 %d 个", carrierName(spec.carrier), spec.addr, proxyPool.Len(), targetPool.Len())
		go acceptCarrierConnections(listener, spec, targetPool, proxyPool, time.Duration(delayMS)*time.Millisecond, num)
	}

	if len(listeners) == 0 {
		return errors.New("所有运营商都未能启动监听（均未扫描到可用转发目标），请检查候选 IP 来源或 -colo 过滤条件")
	}

	select {}
}

func loadCandidateIPs(ipsType string, random bool) ([]string, error) {
	var url string
	var filename string
	switch ipsType {
	case "6":
		filename = "ips-v6.txt"
		url = "https://raw.githubusercontent.com/tdxf1/cfnat.go/main/ips-v6.txt"
	case "4":
		filename = "ips-v4.txt"
		url = "https://raw.githubusercontent.com/tdxf1/cfnat.go/main/ips-v4.txt"
	default:
		return nil, fmt.Errorf("无效的IP类型。请使用 '4' 或 '6'")
	}

	var content string
	var err error
	if _, err = os.Stat(filename); os.IsNotExist(err) {
		fmt.Printf("文件 %s 不存在，正在从 URL %s 下载数据\n", filename, url)
		content, err = getURLContent(url)
		if err != nil {
			return nil, fmt.Errorf("获取URL内容出错: %w", err)
		}
		if err = saveToFile(filename, content); err != nil {
			return nil, fmt.Errorf("保存文件出错: %w", err)
		}
	} else {
		content, err = getFileContent(filename)
		if err != nil {
			return nil, fmt.Errorf("读取本地文件出错: %w", err)
		}
	}

	if random {
		ipList := parseIPList(content)
		switch ipsType {
		case "6":
			return getRandomIPv6s(ipList), nil
		case "4":
			return getRandomIPv4s(ipList), nil
		}
	}
	ipList, err := readIPs(filename)
	if err != nil {
		return nil, fmt.Errorf("读取IP出错: %w", err)
	}
	return ipList, nil
}

func scanCarrierTargets(carrier string, ipList []string, locationMap map[string]location, maxThreads int, proxyPool *BaiduProxyPool, coloFilter string, ipCount int) []result {
	log.Printf("%s 开始扫描转发 IP，百度代理池: %s", carrierName(carrier), strings.Join(proxyPool.Addresses(), ","))
	results := scanIPs(ipList, locationMap, maxThreads, proxyPool)
	if len(results) == 0 {
		log.Printf("%s 未发现有效转发 IP", carrierName(carrier))
		return nil
	}

	if coloFilter != "" {
		filters := strings.Split(coloFilter, ",")
		var filteredResults []result
		for _, r := range results {
			for _, filter := range filters {
				if strings.EqualFold(r.dataCenter, strings.TrimSpace(filter)) {
					filteredResults = append(filteredResults, r)
					break
				}
			}
		}
		results = filteredResults
	}

	sort.Slice(results, func(i, j int) bool {
		return results[i].tcpDuration < results[j].tcpDuration
	})

	if ipCount > 0 && len(results) > ipCount {
		results = results[:ipCount]
	}

	fmt.Printf("%s IP 地址 | 数据中心 | 地区 | 城市 | 延迟\n", carrierName(carrier))
	for _, r := range results {
		fmt.Printf("%s | %s | %s | %s | %s | %s\n", carrierName(carrier), r.ip, r.dataCenter, r.region, r.city, r.latency)
	}

	return results
}

// acceptCarrierConnections 接受连接失败时：listener 已关闭则直接退出该 goroutine，
// 其他错误则短暂 sleep 后重试，避免忙等占满 CPU。
func acceptCarrierConnections(listener net.Listener, spec carrierListenSpec, targetPool *TargetPool, proxyPool *BaiduProxyPool, delay time.Duration, maxAttempts int) {
	for {
		conn, err := listener.Accept()
		if err != nil {
			if opErr, ok := err.(*net.OpError); ok && opErr.Err.Error() == "use of closed network connection" {
				log.Printf("%s 监听已关闭，接受连接 goroutine 退出", carrierName(spec.carrier))
				return
			}
			log.Printf("%s 接受连接失败: %v", carrierName(spec.carrier), err)
			time.Sleep(200 * time.Millisecond)
			continue
		}
		clientAddr := conn.RemoteAddr().String()
		atomic.AddInt32(&activeConnections, 1)
		log.Printf("%s 客户端来源: %s 连接建立，当前活跃连接数: %d", carrierName(spec.carrier), clientAddr, atomic.LoadInt32(&activeConnections))
		go handlePoolConnection(conn, spec.carrier, targetPool, proxyPool, delay, maxAttempts)
	}
}

func handlePoolConnection(conn net.Conn, carrier string, targetPool *TargetPool, proxyPool *BaiduProxyPool, delay time.Duration, maxAttempts int) {
	defer func() {
		clientAddr := conn.RemoteAddr().String()
		atomic.AddInt32(&activeConnections, -1)
		log.Printf("%s 客户端来源: %s 连接关闭，当前活跃连接数: %d", carrierName(carrier), clientAddr, atomic.LoadInt32(&activeConnections))
		conn.Close()
	}()

	targets := targetPool.PickTargets(maxAttempts)
	if len(targets) == 0 {
		log.Printf("%s 没有可用转发目标，关闭客户端连接", carrierName(carrier))
		return
	}

	var bestConn net.Conn
	var bestTarget *targetEndpoint
	var bestDelay time.Duration

	for _, target := range targets {
		atomic.AddInt32(&target.active, 1)
		start := time.Now()
		ctx, cancel := context.WithTimeout(context.Background(), delay)
		forwardConn, err := dialTarget(ctx, "tcp", target.addr, delay, proxyPool)
		cancel()
		elapsed := time.Since(start)
		if err != nil {
			atomic.AddInt32(&target.active, -1)
			target.recordFailure(elapsed)
			log.Printf("%s 连接目标 %s 失败或超时 %d ms: %v", carrierName(carrier), target.addr, delay.Milliseconds(), err)
			continue
		}
		target.recordSuccess(elapsed)
		if bestConn == nil || elapsed < bestDelay {
			if bestConn != nil {
				bestConn.Close()
				atomic.AddInt32(&bestTarget.active, -1)
			}
			bestConn = forwardConn
			bestTarget = target
			bestDelay = elapsed
		} else {
			forwardConn.Close()
			atomic.AddInt32(&target.active, -1)
		}
	}

	if bestConn == nil {
		log.Printf("%s 未找到符合延迟要求的连接，关闭客户端连接", carrierName(carrier))
		return
	}
	defer atomic.AddInt32(&bestTarget.active, -1)

	log.Printf("%s 选择目标: %s 延迟: %d ms", carrierName(carrier), bestTarget.addr, bestDelay.Milliseconds())
	pipeConnections(conn, bestConn)
}

// buildDefaultBaiduPool 构建单端口模式下的百度代理池：多 DNS 解析器聚合解析候选地址，
// 逐个扫描连通性并按延迟排序，截取最优的 maxNodes 个。若解析或扫描都拿不到可用节点，
// 回退为直接使用域名:端口这一个地址；回退前会先对它跑一次连通性测试并记录日志，
// 这样即使它本身不可用，也能返回它作为最后手段，让排障时能第一时间定位问题根源。
func buildDefaultBaiduPool(domain string, port int, scanTarget string, maxNodes int, maxThreads int) *BaiduProxyPool {
	candidates := resolveBaiduProxyCandidates(domain, port, nil)
	fallbackAddr := ensureHostPort(domain, port)

	if len(candidates) == 0 {
		log.Printf("百度前置代理未解析到任何候选 IP，尝试验证域名回退地址: %s", fallbackAddr)
		if scanned := scanBaiduProxyAddrs("default", []string{fallbackAddr}, scanTarget, timeout, 1); len(scanned) > 0 {
			log.Printf("域名回退地址验证可用: %s", fallbackAddr)
		} else {
			log.Printf("警告：域名回退地址 %s 连通性验证失败，仍将使用它作为最后手段，转发大概率会失败，请检查网络/百度代理服务状态", fallbackAddr)
		}
		return NewBaiduProxyPool("default", []string{fallbackAddr})
	}

	log.Printf("百度前置代理候选池: %s", strings.Join(candidates, ","))
	scanned := scanBaiduProxyAddrs("default", candidates, scanTarget, timeout, maxThreads)
	if maxNodes > 0 && len(scanned) > maxNodes {
		scanned = scanned[:maxNodes]
	}

	if len(scanned) == 0 {
		log.Printf("百度前置代理没有扫描到可用节点，尝试验证域名回退地址: %s", fallbackAddr)
		if fallbackScanned := scanBaiduProxyAddrs("default", []string{fallbackAddr}, scanTarget, timeout, 1); len(fallbackScanned) > 0 {
			log.Printf("域名回退地址验证可用: %s", fallbackAddr)
		} else {
			log.Printf("警告：域名回退地址 %s 连通性验证也失败，仍将使用它作为最后手段，转发大概率会失败，请检查网络/百度代理服务状态", fallbackAddr)
		}
		return NewBaiduProxyPool("default", []string{fallbackAddr})
	}

	log.Printf("百度前置代理可用池: %s", strings.Join(scanned, ","))
	return NewBaiduProxyPool("default", scanned)
}

func buildBaiduPoolsByCarrier(extraResolvers map[string][]string, domain string, port int, scanTarget string, maxNodes int, maxThreads int) map[string]*BaiduProxyPool {
	candidates := resolveBaiduProxyCandidates(domain, port, extraResolvers)
	if len(candidates) == 0 {
		log.Printf("没有解析到任何百度代理 IP")
		return nil
	}

	grouped := make(map[string][]string)
	for _, addr := range candidates {
		host, _, err := net.SplitHostPort(addr)
		if err != nil {
			log.Printf("跳过无效百度代理地址 %s: %v", addr, err)
			continue
		}
		carrier, asn, asName, err := classifyCarrierByIP(host)
		if err != nil {
			log.Printf("百度代理候选归属未知: %s: %v", addr, err)
			continue
		}
		if carrier == "" {
			log.Printf("百度代理候选未归入三大运营商: %s -> AS%s %s", addr, asn, asName)
			continue
		}
		log.Printf("百度代理候选归属: %s -> AS%s %s -> %s", addr, asn, asName, carrierName(carrier))
		grouped[carrier] = append(grouped[carrier], addr)
	}

	pools := make(map[string]*BaiduProxyPool)
	for carrier, addrs := range grouped {
		addrs = dedupeStrings(addrs)
		log.Printf("%s 百度代理候选池: %s", carrierName(carrier), strings.Join(addrs, ","))
		scanned := scanBaiduProxyAddrs(carrier, addrs, scanTarget, timeout, maxThreads)
		if maxNodes > 0 && len(scanned) > maxNodes {
			scanned = scanned[:maxNodes]
		}
		if len(scanned) == 0 {
			log.Printf("%s 没有扫描到可用百度代理 IP", carrierName(carrier))
			continue
		}
		log.Printf("%s 百度代理可用池: %s", carrierName(carrier), strings.Join(scanned, ","))
		pools[carrier] = NewBaiduProxyPool(carrier, scanned)
	}
	return pools
}

func resolveBaiduProxyCandidates(domain string, port int, extraResolvers map[string][]string) []string {
	resolvers := collectBaiduResolvers(extraResolvers)

	type lookupResult struct {
		source string
		ips    []string
		err    error
	}

	results := make(chan lookupResult, len(resolvers)+1)
	var wg sync.WaitGroup

	wg.Add(1)
	go func() {
		defer wg.Done()
		// 注意：net.LookupHost 内部使用 context.Background()，没有任何超时；
		// 若系统 DNS 异常挂起（例如被防火墙静默丢包），该 goroutine 会永久阻塞，
		// 导致下面的 wg.Wait()/close(results) 永远不会执行，从而使整个程序启动挂死。
		// 这里显式带上超时，与其他自定义 resolver 保持一致。
		ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
		defer cancel()
		ips, err := net.DefaultResolver.LookupHost(ctx, domain)
		results <- lookupResult{source: "system", ips: ips, err: err}
	}()

	for _, resolverAddr := range resolvers {
		wg.Add(1)
		go func(addr string) {
			defer wg.Done()
			ips, err := lookupHostWithResolver(domain, addr)
			results <- lookupResult{source: addr, ips: ips, err: err}
		}(resolverAddr)
	}

	go func() {
		wg.Wait()
		close(results)
	}()

	var addrs []string
	for result := range results {
		if result.err != nil {
			log.Printf("解析百度代理域名失败 resolver=%s: %v", result.source, result.err)
			continue
		}
		var parsed []string
		for _, ip := range result.ips {
			if net.ParseIP(ip) == nil {
				continue
			}
			addr := ensureHostPort(ip, port)
			addrs = append(addrs, addr)
			parsed = append(parsed, addr)
		}
		if len(parsed) > 0 {
			log.Printf("解析百度代理域名成功 resolver=%s: %s", result.source, strings.Join(parsed, ","))
		}
	}

	addrs = dedupeStrings(addrs)
	sort.Strings(addrs)
	log.Printf("百度代理聚合候选 IP 数量: %d", len(addrs))
	return addrs
}

func collectBaiduResolvers(extraResolvers map[string][]string) []string {
	var resolvers []string
	resolvers = append(resolvers, defaultBaiduResolvers...)
	for _, values := range defaultCarrierResolvers {
		resolvers = append(resolvers, values...)
	}
	for _, values := range extraResolvers {
		resolvers = append(resolvers, values...)
	}
	for i, resolverAddr := range resolvers {
		resolvers[i] = ensureHostPort(resolverAddr, 53)
	}
	return dedupeStrings(resolvers)
}

func classifyCarrierByIP(ip string) (string, string, string, error) {
	asn, err := lookupASN(ip)
	if err != nil {
		return "", "", "", err
	}
	if asn == "" {
		return "", "", "", fmt.Errorf("没有查到 ASN")
	}
	asName, err := lookupASName(asn)
	if err != nil {
		return "", asn, "", err
	}
	carrier := carrierFromASN(asn, asName)
	return carrier, asn, asName, nil
}

// asnLookupTimeout 用于 lookupASN/lookupASName 这两个对 team-cymru.com 的 DNS TXT 查询。
// 注意：net.LookupTXT 内部同样使用 context.Background()，没有任何超时；而这两个函数在
// buildBaiduPoolsByCarrier 里是对每个候选 IP 顺序（非并发）调用的，一旦 cymru.com 的查询被
// 防火墙静默丢弃或长期无响应，第一个候选就会把整个运营商分池模式的启动流程永久卡住。
const asnLookupTimeout = 3 * time.Second

func lookupASN(ip string) (string, error) {
	parsed := net.ParseIP(ip)
	if parsed == nil {
		return "", fmt.Errorf("无效 IP: %s", ip)
	}
	ipv4 := parsed.To4()
	if ipv4 == nil {
		return "", fmt.Errorf("暂不支持 IPv6 ASN 查询: %s", ip)
	}
	query := fmt.Sprintf("%d.%d.%d.%d.origin.asn.cymru.com", ipv4[3], ipv4[2], ipv4[1], ipv4[0])
	ctx, cancel := context.WithTimeout(context.Background(), asnLookupTimeout)
	defer cancel()
	txts, err := net.DefaultResolver.LookupTXT(ctx, query)
	if err != nil {
		return "", err
	}
	if len(txts) == 0 {
		return "", nil
	}
	fields := strings.Split(txts[0], "|")
	if len(fields) == 0 {
		return "", nil
	}
	return strings.TrimSpace(fields[0]), nil
}

func lookupASName(asn string) (string, error) {
	ctx, cancel := context.WithTimeout(context.Background(), asnLookupTimeout)
	defer cancel()
	txts, err := net.DefaultResolver.LookupTXT(ctx, "AS"+strings.TrimSpace(asn)+".asn.cymru.com")
	if err != nil {
		return "", err
	}
	if len(txts) == 0 {
		return "", nil
	}
	fields := strings.Split(txts[0], "|")
	if len(fields) < 5 {
		return strings.TrimSpace(txts[0]), nil
	}
	return strings.TrimSpace(fields[4]), nil
}

func carrierFromASN(asn string, asName string) string {
	asn = strings.TrimSpace(asn)
	name := strings.ToUpper(asName)
	switch asn {
	case "9808", "56040", "56041", "56042", "56044", "56046", "56047", "56048", "56050", "56052", "56055", "56056", "56057", "56058", "56059", "56060", "56061", "56062":
		return carrierMobile
	case "4134", "4809", "4812", "4816", "4811", "4813", "4815", "23724", "134756":
		return carrierTelecom
	case "4837", "4808", "9929", "10099", "17621", "136958", "140717":
		return carrierUnicom
	}
	switch {
	case strings.Contains(name, "MOBILE") || strings.Contains(name, "CMNET") || strings.Contains(name, "CMCC") || strings.Contains(name, "CHINAMOBILE"):
		return carrierMobile
	case strings.Contains(name, "TELECOM") || strings.Contains(name, "CHINANET") || strings.Contains(name, "CHINA NET") || strings.Contains(name, "CN2"):
		return carrierTelecom
	case strings.Contains(name, "UNICOM") || strings.Contains(name, "CHINA169") || strings.Contains(name, "CNCGROUP") || strings.Contains(name, "NETCOM"):
		return carrierUnicom
	default:
		return ""
	}
}

func lookupHostWithResolver(host string, resolverAddr string) ([]string, error) {
	resolver := &net.Resolver{
		PreferGo: true,
		Dial: func(ctx context.Context, network, address string) (net.Conn, error) {
			dialer := &net.Dialer{Timeout: timeout}
			return dialer.DialContext(ctx, "udp", resolverAddr)
		},
	}
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	return resolver.LookupHost(ctx, host)
}

func scanBaiduProxyAddrs(carrier string, addrs []string, scanTarget string, dialTimeout time.Duration, maxThreads int) []string {
	type scanResult struct {
		addr    string
		latency time.Duration
	}

	var wg sync.WaitGroup
	var mu sync.Mutex
	var results []scanResult

	if maxThreads <= 0 {
		maxThreads = 1
	}
	thread := make(chan struct{}, maxThreads)

	for _, addr := range addrs {
		wg.Add(1)
		thread <- struct{}{}
		go func(nodeAddr string) {
			defer func() {
				<-thread
				wg.Done()
			}()
			ctx, cancel := context.WithTimeout(context.Background(), dialTimeout)
			defer cancel()
			start := time.Now()
			conn, err := dialBaiduTunnelViaNode(ctx, nodeAddr, scanTarget, dialTimeout)
			elapsed := time.Since(start)
			if err != nil {
				log.Printf("%s 百度代理节点不可用 %s: %v", carrierName(carrier), nodeAddr, err)
				return
			}
			conn.Close()
			mu.Lock()
			results = append(results, scanResult{addr: nodeAddr, latency: elapsed})
			mu.Unlock()
			log.Printf("%s 百度代理节点可用 %s 延迟 %d ms", carrierName(carrier), nodeAddr, elapsed.Milliseconds())
		}(addr)
	}
	wg.Wait()

	sort.Slice(results, func(i, j int) bool {
		return results[i].latency < results[j].latency
	})

	scanned := make([]string, 0, len(results))
	for _, result := range results {
		scanned = append(scanned, result.addr)
	}
	return scanned
}

func parseCarrierListens(raw string) ([]carrierListenSpec, error) {
	var specs []carrierListenSpec
	seen := make(map[string]struct{})
	for _, part := range strings.Split(raw, ",") {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		carrier, addr, ok := strings.Cut(part, "=")
		if !ok {
			return nil, fmt.Errorf("无效项 %q，格式应为 carrier=host:port", part)
		}
		carrier = normalizeCarrier(carrier)
		if carrier == "" {
			return nil, fmt.Errorf("未知运营商 %q", part)
		}
		addr = strings.TrimSpace(addr)
		if addr == "" {
			return nil, fmt.Errorf("%s 的监听地址为空", carrierName(carrier))
		}
		if _, ok := seen[carrier]; ok {
			return nil, fmt.Errorf("%s 重复配置", carrierName(carrier))
		}
		seen[carrier] = struct{}{}
		specs = append(specs, carrierListenSpec{carrier: carrier, addr: addr})
	}
	if len(specs) == 0 {
		return nil, errors.New("未配置任何运营商监听端口")
	}
	return specs, nil
}

func parseCarrierResolvers(raw string) (map[string][]string, error) {
	resolvers := make(map[string][]string)
	if strings.TrimSpace(raw) == "" {
		return resolvers, nil
	}
	for _, part := range strings.Split(raw, ",") {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		carrier, value, ok := strings.Cut(part, "=")
		if !ok {
			return nil, fmt.Errorf("无效项 %q，格式应为 carrier=dns1|dns2", part)
		}
		carrier = normalizeCarrier(carrier)
		if carrier == "" {
			return nil, fmt.Errorf("未知运营商 %q", part)
		}
		for _, resolverAddr := range strings.Split(value, "|") {
			resolverAddr = strings.TrimSpace(resolverAddr)
			if resolverAddr == "" {
				continue
			}
			resolvers[carrier] = append(resolvers[carrier], ensureHostPort(resolverAddr, 53))
		}
	}
	return resolvers, nil
}

func normalizeCarrier(value string) string {
	switch strings.ToLower(strings.TrimSpace(value)) {
	case carrierMobile, "cmcc", "china-mobile", "移动", "中国移动":
		return carrierMobile
	case carrierTelecom, "ct", "chinanet", "china-telecom", "电信", "中国电信":
		return carrierTelecom
	case carrierUnicom, "cu", "cuc", "china-unicom", "联通", "中国联通":
		return carrierUnicom
	default:
		return ""
	}
}

func carrierName(carrier string) string {
	if name, ok := carrierDisplayNames[carrier]; ok {
		return name
	}
	return carrier
}

func ensureHostPort(addr string, port int) string {
	addr = strings.TrimSpace(addr)
	if addr == "" {
		return addr
	}
	if _, _, err := net.SplitHostPort(addr); err == nil {
		return addr
	}
	return net.JoinHostPort(strings.Trim(addr, "[]"), strconv.Itoa(port))
}

func dedupeStrings(values []string) []string {
	seen := make(map[string]struct{}, len(values))
	var out []string
	for _, value := range values {
		value = strings.TrimSpace(value)
		if value == "" {
			continue
		}
		if _, ok := seen[value]; ok {
			continue
		}
		seen[value] = struct{}{}
		out = append(out, value)
	}
	return out
}

// loadLocations 加载位置信息，使用函数封装确保 defer 正确执行
func loadLocations() ([]location, error) {
	var locations []location
	if _, err := os.Stat("locations.json"); os.IsNotExist(err) {
		fmt.Println("本地 locations.json 不存在\n正在从 https://raw.githubusercontent.com/tdxf1/cfnat.go/main/ 下载 locations.json")
		resp, err := http.Get("https://raw.githubusercontent.com/tdxf1/cfnat.go/main/locations.json")
		if err != nil {
			return nil, fmt.Errorf("无法从URL中获取JSON: %v", err)
		}
		defer resp.Body.Close()
		body, err := io.ReadAll(resp.Body)
		if err != nil {
			return nil, fmt.Errorf("无法读取响应体: %v", err)
		}
		err = json.Unmarshal(body, &locations)
		if err != nil {
			return nil, fmt.Errorf("无法解析JSON: %v", err)
		}
		file, err := os.Create("locations.json")
		if err != nil {
			return nil, fmt.Errorf("无法创建文件: %v", err)
		}
		defer file.Close()
		_, err = file.Write(body)
		if err != nil {
			return nil, fmt.Errorf("无法写入文件: %v", err)
		}
	} else {
		file, err := os.Open("locations.json")
		if err != nil {
			return nil, fmt.Errorf("无法打开文件: %v", err)
		}
		defer file.Close()
		body, err := io.ReadAll(file)
		if err != nil {
			return nil, fmt.Errorf("无法读取文件: %v", err)
		}
		err = json.Unmarshal(body, &locations)
		if err != nil {
			return nil, fmt.Errorf("无法解析JSON: %v", err)
		}
	}
	return locations, nil
}

// scanIPs 扫描 IP 列表并返回结果
func scanIPs(ipList []string, locationMap map[string]location, maxThreads int, proxyPool *BaiduProxyPool) []result {
	var wg sync.WaitGroup
	var mu sync.Mutex
	var results []result
	thread := make(chan struct{}, maxThreads)

	var count int32
	total := len(ipList)

	for _, ip := range ipList {
		wg.Add(1)
		thread <- struct{}{}
		go func(ipAddr string) {
			defer func() {
				<-thread
				wg.Done()
				current := atomic.AddInt32(&count, 1)
				percentage := float64(current) / float64(total) * 100
				fmt.Printf("已完成: %d 总数: %d 已完成: %.2f%%\r", current, total, percentage)
				if int(current) == total {
					fmt.Printf("已完成: %d 总数: %d 已完成: %.2f%%\n", current, total, percentage)
				}
			}()

			start := time.Now()
			ctx, cancel := context.WithTimeout(context.Background(), timeout)
			defer cancel()
			conn, err := dialTarget(ctx, "tcp", net.JoinHostPort(ipAddr, "80"), timeout, proxyPool)
			if err != nil {
				return
			}
			defer conn.Close()

			tcpDuration := time.Since(start)

			// 通过根路径响应头里的 CF-RAY 提取机房信息
			requestURL := "http://" + net.JoinHostPort(ipAddr, "80")
			req, err := http.NewRequest("GET", requestURL, nil)
			if err != nil {
				return
			}
			req.Header.Set("User-Agent", "Mozilla/5.0")
			req.Close = true

			conn.SetDeadline(time.Now().Add(maxDuration))
			err = req.Write(conn)
			if err != nil {
				return
			}

			reader := bufio.NewReader(conn)
			resp, err := http.ReadResponse(reader, req)
			if err != nil {
				return
			}
			defer resp.Body.Close()

			cfRay := strings.TrimSpace(resp.Header.Get("CF-RAY"))
			if cfRay == "" {
				return
			}
			parts := strings.Split(cfRay, "-")
			if len(parts) < 2 {
				return
			}
			dataCenter := strings.TrimSpace(parts[len(parts)-1])
			if dataCenter == "" {
				return
			}

			loc, ok := locationMap[dataCenter]
			mu.Lock()
			if ok {
				fmt.Printf("发现有效IP %s 位置信息 %s 延迟 %d 毫秒\n", ipAddr, loc.City, tcpDuration.Milliseconds())
				results = append(results, result{ipAddr, dataCenter, loc.Region, loc.City, fmt.Sprintf("%d ms", tcpDuration.Milliseconds()), tcpDuration})
			} else {
				fmt.Printf("发现有效IP %s 位置信息未知 延迟 %d 毫秒\n", ipAddr, tcpDuration.Milliseconds())
				results = append(results, result{ipAddr, dataCenter, "", "", fmt.Sprintf("%d ms", tcpDuration.Milliseconds()), tcpDuration})
			}
			mu.Unlock()
		}(ip)
	}
	wg.Wait()
	return results
}

func dialTarget(ctx context.Context, network, targetAddr string, dialTimeout time.Duration, proxyPool *BaiduProxyPool) (net.Conn, error) {
	if proxyPool != nil {
		return proxyPool.Dial(ctx, targetAddr, dialTimeout)
	}
	dialer := &net.Dialer{
		Timeout:   dialTimeout,
		KeepAlive: 0,
	}
	return dialer.DialContext(ctx, network, targetAddr)
}

// dialBaiduTunnelViaNode 使用固定百度 CONNECT 参数建立前置隧道。
func dialBaiduTunnelViaNode(ctx context.Context, nodeAddr string, targetAddr string, dialTimeout time.Duration) (net.Conn, error) {
	dialer := &net.Dialer{
		Timeout:   dialTimeout,
		KeepAlive: 0,
	}
	conn, err := dialer.DialContext(ctx, "tcp", nodeAddr)
	if err != nil {
		return nil, fmt.Errorf("连接百度前置代理失败: %w", err)
	}

	deadline := time.Now().Add(dialTimeout)
	if ctxDeadline, ok := ctx.Deadline(); ok && ctxDeadline.Before(deadline) {
		deadline = ctxDeadline
	}
	if err := conn.SetDeadline(deadline); err != nil {
		conn.Close()
		return nil, fmt.Errorf("设置百度前置代理超时失败: %w", err)
	}

	connectReq := fmt.Sprintf(
		"CONNECT %s HTTP/1.1\r\n"+
			"Host: %s\r\n"+
			"X-T5-Auth: %s\r\n"+
			"User-Agent: %s\r\n"+
			"Proxy-Connection: keep-alive\r\n"+
			"Connection: keep-alive\r\n"+
			"\r\n",
		targetAddr,
		baiduFakeHost,
		baiduAuthToken,
		baiduUserAgent,
	)

	if _, err := conn.Write([]byte(connectReq)); err != nil {
		conn.Close()
		return nil, fmt.Errorf("写入百度前置代理 CONNECT 失败: %w", err)
	}

	resp, err := http.ReadResponse(bufio.NewReader(conn), nil)
	if err != nil {
		conn.Close()
		return nil, fmt.Errorf("读取百度前置代理 CONNECT 响应失败: %w", err)
	}
	resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		conn.Close()
		return nil, fmt.Errorf("百度前置代理 CONNECT 被拒绝: %s", resp.Status)
	}

	if err := conn.SetDeadline(time.Time{}); err != nil {
		conn.Close()
		return nil, fmt.Errorf("清除百度前置代理超时失败: %w", err)
	}

	return conn, nil
}

// 获取URL内容
func getURLContent(url string) (string, error) {
	resp, err := http.Get(url)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("HTTP请求失败，状态码: %d", resp.StatusCode)
	}

	var content strings.Builder
	scanner := bufio.NewScanner(resp.Body)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line != "" {
			content.WriteString(line + "\n")
		}
	}
	if err := scanner.Err(); err != nil {
		return "", err
	}

	return content.String(), nil
}

// 从本地文件读取内容
func getFileContent(filename string) (string, error) {
	data, err := os.ReadFile(filename)
	if err != nil {
		return "", err
	}
	return string(data), nil
}

// 将内容保存到本地文件
func saveToFile(filename, content string) error {
	return os.WriteFile(filename, []byte(content), 0644)
}

// 解析IP列表，跳过空行
func parseIPList(content string) []string {
	scanner := bufio.NewScanner(strings.NewReader(content))
	var ipList []string
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line != "" {
			ipList = append(ipList, line)
		}
	}
	return ipList
}

func nextRandomIntn(n int) int {
	randomMu.Lock()
	defer randomMu.Unlock()
	return randomGenerator.Intn(n)
}

// 从每个 CIDR 子网中随机提取一个 IPv4 代表地址
func getRandomIPv4s(ipList []string) []string {
	var randomIPs []string
	for _, subnet := range ipList {
		subnet = strings.TrimSpace(subnet)
		if subnet == "" {
			continue
		}
		ip, err := randomIPInCIDR(subnet, net.IPv4len)
		if err != nil {
			log.Printf("跳过无效的 IPv4 网段 %q: %v", subnet, err)
			continue
		}
		randomIPs = append(randomIPs, ip)
	}
	return randomIPs
}

// 从每个 CIDR 子网中随机提取一个 IPv6 代表地址
func getRandomIPv6s(ipList []string) []string {
	var randomIPs []string
	for _, subnet := range ipList {
		subnet = strings.TrimSpace(subnet)
		if subnet == "" {
			continue
		}
		ip, err := randomIPInCIDR(subnet, net.IPv6len)
		if err != nil {
			log.Printf("跳过无效的 IPv6 网段 %q: %v", subnet, err)
			continue
		}
		randomIPs = append(randomIPs, ip)
	}
	return randomIPs
}

// randomIPInCIDR 在给定 CIDR 网段内，按其真实前缀长度随机生成一个地址（仅随机化主机位，网络位保持不变）。
// 原实现通过 TrimSuffix("/24"或"/48") 加字符串分割来拼接地址，一旦输入不是精确的 /24（IPv4）
// 或 /48（IPv6），或 IPv6 地址使用了 "::" 压缩写法，就会静默按错误的前缀处理，
// 有可能拼出网络位被破坏、或对大网段采样覆盖率远低于预期的地址。这里改用 net.ParseCIDR 正确解析。
func randomIPInCIDR(cidr string, wantLen int) (string, error) {
	if !strings.Contains(cidr, "/") {
		ip := net.ParseIP(cidr)
		if ip == nil {
			return "", fmt.Errorf("无效 IP")
		}
		return ip.String(), nil
	}

	ip, ipNet, err := net.ParseCIDR(cidr)
	if err != nil {
		return "", err
	}
	base := ip.Mask(ipNet.Mask)

	switch wantLen {
	case net.IPv4len:
		v4 := base.To4()
		if v4 == nil {
			return "", fmt.Errorf("不是有效的 IPv4 网段")
		}
		base = v4
	case net.IPv6len:
		if base.To4() != nil {
			return "", fmt.Errorf("不是有效的 IPv6 网段")
		}
		v6 := base.To16()
		if v6 == nil {
			return "", fmt.Errorf("不是有效的 IPv6 网段")
		}
		base = v6
	default:
		return "", fmt.Errorf("不支持的地址长度: %d", wantLen)
	}

	ones, bits := ipNet.Mask.Size()
	hostBits := bits - ones
	result := make(net.IP, len(base))
	copy(result, base)

	for i := len(result) - 1; i >= 0 && hostBits > 0; i-- {
		bitsInByte := 8
		if hostBits < 8 {
			bitsInByte = hostBits
		}
		randVal := byte(nextRandomIntn(1 << uint(bitsInByte)))
		mask := byte((1 << uint(bitsInByte)) - 1)
		result[i] = (result[i] &^ mask) | (randVal & mask)
		hostBits -= bitsInByte
	}
	return result.String(), nil
}

// 从CIDR中拆分出所有IP
func readIPs(filename string) ([]string, error) {
	file, err := os.Open(filename)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	var ips []string
	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		// 跳过空行
		if line == "" {
			continue
		}
		if strings.Contains(line, "/") {
			ipAddr, ipNet, err := net.ParseCIDR(line)
			if err != nil {
				return nil, err
			}
			// 使用新变量避免遮蔽
			for currentIP := ipAddr.Mask(ipNet.Mask); ipNet.Contains(currentIP); incrementIP(currentIP) {
				ips = append(ips, currentIP.String())
			}
		} else {
			ips = append(ips, line)
		}
	}
	if err := scanner.Err(); err != nil {
		return nil, err
	}
	return ips, nil
}

// 增加IP
func incrementIP(ip net.IP) {
	for j := len(ip) - 1; j >= 0; j-- {
		ip[j]++
		if ip[j] > 0 {
			break
		}
	}
}

func generateTargets(ip string, port int, num int) []string {
	targets := make([]string, num)
	address := net.JoinHostPort(ip, fmt.Sprintf("%d", port))
	for i := 0; i < num; i++ {
		targets[i] = address
	}
	return targets
}

func checkValidIP(ip string, port int, useTLS bool, domain string, code int, proxyPool *BaiduProxyPool) bool {
	address := net.JoinHostPort(ip, fmt.Sprintf("%d", port))
	targetURL := fmt.Sprintf("http://%s", domain)
	if useTLS {
		targetURL = fmt.Sprintf("https://%s", domain)
	}

	cacheKey := fmt.Sprintf("%s|%s", proxyPool.CacheKey(), address)
	clientAny, loaded := validIPClientCache.Load(cacheKey)
	var client *http.Client
	if loaded {
		client = clientAny.(*http.Client)
	} else {
		transport := &http.Transport{
			TLSClientConfig:   &tls.Config{InsecureSkipVerify: true},
			DisableKeepAlives: true,
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				log.Printf("尝试连接 IP: %s 端口: %d", ip, port)
				// 注意：此处故意使用固定的 maxDuration（2秒），而不是用户的 -delay 参数。
				// -delay 是"转发延迟阈值"（用于判断已建立连接是否够快），数值通常很小（默认300ms）。
				// 而这里是"IP 是否可达/可用"的探测性校验，需要更宽松的超时，
				// 否则在默认配置或经百度代理隧道转发时，几乎所有 IP 都会被误判为无效。
				return dialTarget(ctx, network, address, maxDuration, proxyPool)
			},
		}
		newClient := &http.Client{
			Timeout:   maxDuration,
			Transport: transport,
		}
		actual, _ := validIPClientCache.LoadOrStore(cacheKey, newClient)
		client = actual.(*http.Client)
	}

	log.Printf("向 URL %s 发送请求以检查 IP %s 是否有效", targetURL, ip)
	resp, err := client.Get(targetURL)
	if err != nil {
		log.Printf("检查 IP %s 时发生错误: %v", ip, err)
		return false
	}
	defer resp.Body.Close()

	log.Printf("IP %s 的检查响应状态码: %d", ip, resp.StatusCode)
	isValid := resp.StatusCode == code
	if isValid {
		log.Printf("IP %s 是有效的", ip)
	} else {
		log.Printf("IP %s 不是有效的", ip)
	}
	return isValid
}

func selectValidIP(ipManager *IPManager, useTLS bool, port int, domain string, code int, proxyPool *BaiduProxyPool) string {
	for _, ip := range ipManager.GetIPAddresses() {
		if checkValidIP(ip, port, useTLS, domain, code, proxyPool) {
			return ip
		}
	}
	return ""
}

// statusCheck 定期自检本地监听端口是否存活；内外层循环都会检查 forwardFailCount，
// 一旦业务转发连续失败达到阈值（>=2，有意设计的激进策略）就立即触发 IP 切换，
// 不必等一整轮自检（可能长达数秒）走完才响应。
func statusCheck(ctx context.Context, localAddr string, useTLS bool, port int, done chan bool, domain string, code int, delay time.Duration, ipManager *IPManager, proxyPool *BaiduProxyPool) {
	_, localPort, _ := net.SplitHostPort(localAddr)
	checkAddr := fmt.Sprintf("127.0.0.1:%s", localPort)

outerLoop:
	for {
		select {
		case <-ctx.Done():
			log.Println("状态检查收到退出信号")
			return
		default:
		}

		if atomic.LoadInt32(&forwardFailCount) >= 2 {
			log.Println("业务转发连续失败，触发 IP 切换")
			atomic.StoreInt32(&forwardFailCount, 0)
			if !ipManager.switchToNextValidIP(useTLS, port, domain, code, proxyPool) {
				log.Println("所有 IP 已用尽，状态检查退出")
				done <- true
				return
			}
			time.Sleep(1 * time.Second)
			continue outerLoop
		}

		failCount := 0
		log.Printf("开始状态检查，目标地址: %s", checkAddr)

		for failCount < 2 {
			select {
			case <-ctx.Done():
				log.Println("状态检查收到退出信号")
				return
			default:
			}

			if atomic.LoadInt32(&forwardFailCount) >= 2 {
				log.Println("业务转发连续失败（内层检测），触发 IP 切换")
				atomic.StoreInt32(&forwardFailCount, 0)
				if !ipManager.switchToNextValidIP(useTLS, port, domain, code, proxyPool) {
					log.Println("所有 IP 已用尽，状态检查退出")
					done <- true
					return
				}
				time.Sleep(1 * time.Second)
				continue outerLoop
			}

			conn, err := net.DialTimeout("tcp", checkAddr, delay)
			if err != nil {
				failCount++
				log.Printf("状态检查失败 (%d/2): 无法连接到 %s 错误: %v", failCount, checkAddr, err)
				time.Sleep(1 * time.Second)
				continue
			}

			// 使用带超时的读取检查
			checkSuccess := make(chan bool, 1)
			go func() {
				reader := bufio.NewReader(conn)
				conn.SetReadDeadline(time.Now().Add(delay + 1*time.Second))
				_, err := reader.ReadString('\n')
				if err != nil {
					if err == io.EOF {
						checkSuccess <- false
					} else if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
						// 超时说明连接保持正常
						checkSuccess <- true
					} else {
						checkSuccess <- false
					}
				} else {
					checkSuccess <- true
				}
			}()

			select {
			case success := <-checkSuccess:
				if success {
					log.Printf("状态检查成功: 连接到 %s 成功", checkAddr)
					failCount = 0
				} else {
					failCount++
					log.Printf("状态检查失败 (%d/2): 服务端断开连接", failCount)
				}
			case <-time.After(delay + 2*time.Second):
				log.Printf("状态检查成功: 连接到 %s 保持稳定", checkAddr)
				failCount = 0
			case <-ctx.Done():
				conn.Close()
				log.Println("状态检查收到退出信号")
				return
			}

			conn.Close()

			if failCount == 0 {
				time.Sleep(2 * time.Second)
				break
			}
		}

		if failCount >= 2 {
			log.Println("连续两次状态检查失败，切换到下一个 IP")
			atomic.StoreInt32(&forwardFailCount, 0)
			if !ipManager.switchToNextValidIP(useTLS, port, domain, code, proxyPool) {
				log.Println("所有 IP 都已检查过，状态检查停止")
				done <- true
				return
			}
		}
	}
}

// 处理客户端连接，尝试连接到指定的转发地址，并选择延迟最低的连接
func handleConnection(conn net.Conn, forwardAddrs []string, delay time.Duration, proxyPool *BaiduProxyPool) {
	defer func() {
		clientAddr := conn.RemoteAddr().String()
		atomic.AddInt32(&activeConnections, -1)
		log.Printf("客户端来源: %s 连接关闭，当前活跃连接数: %d", clientAddr, atomic.LoadInt32(&activeConnections))
		conn.Close()
	}()

	type connResult struct {
		conn   net.Conn
		addr   string
		delay  time.Duration
		errMsg string
	}

	results := make(chan connResult, len(forwardAddrs))

	// 并发尝试连接每个转发地址
	for _, addr := range forwardAddrs {
		go func(targetAddr string) {
			start := time.Now()
			ctx, cancel := context.WithTimeout(context.Background(), delay)
			defer cancel()
			forwardConn, err := dialTarget(ctx, "tcp", targetAddr, delay, proxyPool)
			elapsed := time.Since(start)
			if err != nil {
				results <- connResult{nil, targetAddr, elapsed, fmt.Sprintf("连接到 %s 失败或延迟超过有效值 %d ms: %v", targetAddr, delay.Milliseconds(), err)}
				return
			}
			results <- connResult{forwardConn, targetAddr, elapsed, ""}
		}(addr)
	}

	var validConns []connResult
	var bestConn net.Conn
	var bestDelay time.Duration
	var bestAddr string

	// 收集结果并找到延迟最低的有效连接
	for i := 0; i < len(forwardAddrs); i++ {
		res := <-results
		if res.conn != nil {
			validConns = append(validConns, res)
			if bestConn == nil || res.delay < bestDelay {
				if bestConn != nil {
					bestConn.Close()
				}
				bestConn = res.conn
				bestDelay = res.delay
				bestAddr = res.addr
			} else {
				res.conn.Close()
			}
		} else {
			log.Printf("错误: %s", res.errMsg)
		}
	}

	log.Println("符合要求的连接:")
	for _, vc := range validConns {
		log.Printf("地址: %s 延迟: %d ms", vc.addr, vc.delay.Milliseconds())
	}

	// 业务转发成功/失败计数
	if bestConn != nil {
		atomic.StoreInt32(&forwardFailCount, 0)
		log.Printf("选择最佳连接: 地址: %s 延迟: %d ms", bestAddr, bestDelay.Milliseconds())
		pipeConnections(conn, bestConn)
	} else {
		atomic.AddInt32(&forwardFailCount, 1)
		log.Println("未找到符合延迟要求的连接，关闭客户端连接")
	}
}

func pipeConnections(src, dst net.Conn) {
	var wg sync.WaitGroup
	var closeOnce sync.Once
	closeBoth := func() {
		closeOnce.Do(func() {
			src.Close()
			dst.Close()
		})
	}
	wg.Add(2)
	go func() {
		defer wg.Done()
		_, _ = io.Copy(src, dst)
		closeBoth()
	}()
	go func() {
		defer wg.Done()
		_, _ = io.Copy(dst, src)
		closeBoth()
	}()
	wg.Wait()
}
