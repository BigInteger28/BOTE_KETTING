package main

import (
	"bufio"
	"fmt"
	"math"
	"math/rand"
	"os"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// ---------- simulatie (zelfde regels als cpu.go) ----------

var elementsDepthArray [256][4]byte
var moveToIndexArray [256]int

func init() {
	elementsDepthArray['W'] = [4]byte{'L', 'A', 'V', 'W'}
	elementsDepthArray['V'] = [4]byte{'W', 'L', 'A', 'V'}
	elementsDepthArray['A'] = [4]byte{'V', 'W', 'L', 'A'}
	elementsDepthArray['L'] = [4]byte{'A', 'V', 'W', 'L'}
	moveToIndexArray['W'] = 0
	moveToIndexArray['V'] = 1
	moveToIndexArray['A'] = 2
	moveToIndexArray['L'] = 3
	moveToIndexArray['D'] = 4
}

var moveWins = [5][5]uint8{
	{0, 1, 0, 2, 0},
	{2, 0, 1, 0, 0},
	{0, 2, 0, 1, 0},
	{1, 0, 2, 0, 0},
	{0, 0, 0, 0, 0},
}

var depthToElement = [5]byte{'W', 'V', 'A', 'L', 'D'}

type Player struct {
	available [5]int
	moves     [13]byte
	moveCount int
}

func getElementFromCode(depth int) byte {
	if depth < 1 || depth > 5 {
		return 0
	}
	return depthToElement[depth-1]
}

func getElementByDepth(prev byte, depth int) byte {
	if depth == 5 {
		return 'D'
	}
	if prev == 0 {
		return 0
	}
	if prev == 'D' {
		prev = 'L'
	}
	return elementsDepthArray[prev][depth-1]
}

func chooseAvailableElement(target byte, available *[5]int) byte {
	if available[moveToIndexArray[target]] > 0 {
		return target
	}
	current := target
	for i := 0; i < 5; i++ {
		current = elementsDepthArray[current][0]
		if available[moveToIndexArray[current]] > 0 {
			return current
		}
	}
	if available[4] > 0 {
		return 'D'
	}
	return 0
}

func getLastElement(available *[5]int) byte {
	for i, c := range depthToElement {
		if available[i] > 0 {
			return c
		}
	}
	return 0
}

func determineWinner(m1, m2 byte) int {
	return int(moveWins[moveToIndexArray[m1]][moveToIndexArray[m2]])
}

// resolveTarget bepaalt het gewenste element voor zet i: een letter (WVALD) is een vaste zet, een cijfer een diepte
// en de zetten van de tegenstander.
func resolveTarget(ch byte, i int, oppMoves []byte) byte {
	if isMoveLetter(ch) {
		return ch // vaste zet (letter)
	}
	digit := int(ch - '0')
	if digit >= 6 {
		base := digit - 5
		if i < 2 {
			return getElementFromCode(base)
		}
		return getElementByDepth(oppMoves[i-2], base)
	}
	if i == 0 {
		return getElementFromCode(digit)
	}
	return getElementByDepth(oppMoves[i-1], digit)
}

// simulateDepthGame: twee diepte-engines (12 cijfers) tegen elkaar, volledige score.
func simulateDepthGame(e1, e2 string) (s1, s2 int) {
	var p1, p2 Player
	p1.available = [5]int{3, 3, 3, 3, 1}
	p2.available = [5]int{3, 3, 3, 3, 1}
	for i := 0; i < 12; i++ {
		t1 := resolveTarget(e1[i], i, p2.moves[:])
		t2 := resolveTarget(e2[i], i, p1.moves[:])
		m1 := chooseAvailableElement(t1, &p1.available)
		m2 := chooseAvailableElement(t2, &p2.available)
		if m1 == 0 || m2 == 0 {
			return -1, -1
		}
		p1.available[moveToIndexArray[m1]]--
		p1.moves[i] = m1
		p2.available[moveToIndexArray[m2]]--
		p2.moves[i] = m2
		switch determineWinner(m1, m2) {
		case 1:
			s1++
		case 2:
			s2++
		}
	}
	m1 := getLastElement(&p1.available)
	m2 := getLastElement(&p2.available)
	switch determineWinner(m1, m2) {
	case 1:
		s1++
	case 2:
		s2++
	}
	return s1, s2
}

// simulateDepthVsFixed: diepte-engine reageert op een vaste 13-zet engine.
func simulateDepthVsFixed(engine, fixed string) (s1, s2 int) {
	p := Player{available: [5]int{3, 3, 3, 3, 1}}
	var moves [13]byte
	for i := 0; i < 12; i++ {
		t := resolveTarget(engine[i], i, []byte(fixed))
		m := chooseAvailableElement(t, &p.available)
		if m == 0 {
			m = getLastElement(&p.available)
		}
		if m != 0 {
			p.available[moveToIndexArray[m]]--
		}
		moves[i] = m
	}
	m := getLastElement(&p.available)
	if m == 0 {
		m = 'W'
	}
	moves[12] = m
	for i := 0; i < 13; i++ {
		switch determineWinner(moves[i], fixed[i]) {
		case 1:
			s1++
		case 2:
			s2++
		}
	}
	return s1, s2
}

// ---------- evaluatie ----------

type result struct {
	engine string
	losses int // aantal verloren matches
	wins   int
	score  int // totaalscore zoals in cpu.go (winst +10, verlies -10)
	avoid  int // aantal keer dat de te vermijden diepte in de engine staat
}

// avoidDigit is de te vermijden diepte ('1'-'9') of 0; wordt per search ingesteld.
var avoidDigit byte

// better: minder verliezen is beter, dan hogere score.
func better(a, b result) bool {
	if a.losses != b.losses {
		return a.losses < b.losses
	}
	if a.avoid != b.avoid {
		return a.avoid < b.avoid
	}
	return a.score > b.score
}

func evaluate(engine string, opponents []string) result {
	r := result{engine: engine}
	if avoidDigit != 0 {
		r.avoid = strings.Count(engine, string(avoidDigit))
	}
	for _, opp := range opponents {
		var s1, s2 int
		if len(opp) == 13 {
			s1, s2 = simulateDepthVsFixed(engine, opp)
		} else {
			s1, s2 = simulateDepthGame(engine, opp)
		}
		if s1 < 0 {
			continue
		}
		diff := s1 - s2
		switch {
		case s1 > s2:
			r.wins++
			r.score += diff + 10
		case s1 < s2:
			r.losses++
			r.score += diff - 10
		default:
			r.score += s1
		}
	}
	return r
}

// ---------- pool met diversiteit ----------

type pool struct {
	mu      sync.Mutex
	items   []result
	max     int
	minDist int  // minimaal verschil over alle 12 posities
	preDist int  // minimaal verschil binnen de eerste prefixLen posities
	prefer  byte // voorkeursbeginzet (W/V/A/L/D) of 0
	need    int  // minimaal aantal engines met die beginzet (1/2 van max)
	// counts[pos][symIdx] = hoe vaak dat teken op die positie in de pool staat
	counts [12][14]int
}

const prefixLen = 5

func prefixHamming(a, b string) int {
	d := 0
	for i := 0; i < prefixLen; i++ {
		if a[i] != b[i] {
			d++
		}
	}
	return d
}

func hamming(a, b string) int {
	d := 0
	for i := 0; i < 12; i++ {
		if a[i] != b[i] {
			d++
		}
	}
	return d
}

func (p *pool) add(r result) {
	for i := 0; i < 12; i++ {
		p.counts[i][symIdx(r.engine[i])]++
	}
	p.items = append(p.items, r)
}

func (p *pool) removeAt(idx int) {
	e := p.items[idx].engine
	for i := 0; i < 12; i++ {
		p.counts[i][symIdx(e[i])]--
	}
	p.items[idx] = p.items[len(p.items)-1]
	p.items = p.items[:len(p.items)-1]
}

func (p *pool) worstIdx() int {
	w := 0
	for i := 1; i < len(p.items); i++ {
		if better(p.items[w], p.items[i]) {
			w = i
		}
	}
	return w
}

// firstMove geeft de beginzet (W/V/A/L/D) van een engine: de letter zelf of het gelijke cijfer 1-5.
func firstMove(e string) byte {
	c := e[0]
	if c >= '1' && c <= '5' {
		return depthToElement[c-'1']
	}
	return c
}

func (p *pool) isPref(e string) bool { return p.prefer != 0 && firstMove(e) == p.prefer }

func (p *pool) prefCount() int {
	n := 0
	for _, it := range p.items {
		if p.isPref(it.engine) {
			n++
		}
	}
	return n
}

// worstWhere geeft het slechtste item waarvoor ok geldt, of -1 als er geen is.
func (p *pool) worstWhere(ok func(result) bool) int {
	w := -1
	for i, it := range p.items {
		if ok(it) && (w < 0 || better(p.items[w], it)) {
			w = i
		}
	}
	return w
}

// offer probeert een kandidaat in de pool te zetten. Geeft true bij opname.
// Is er een voorkeursbeginzet, dan blijven minstens `need` engines (1/2) met die beginzet.
func (p *pool) offer(r result) bool {
	p.mu.Lock()
	defer p.mu.Unlock()

	candPref := p.isPref(r.engine)
	pref := p.prefCount()

	var near []int
	nearPref := 0
	for i, it := range p.items {
		if hamming(it.engine, r.engine) < p.minDist || prefixHamming(it.engine, r.engine) < p.preDist {
			if !better(r, it) {
				return false // een even goede of betere buur bestaat al
			}
			near = append(near, i)
			if p.isPref(it.engine) {
				nearPref++
			}
		}
	}
	if len(near) > 0 {
		if p.prefer != 0 {
			after := pref - nearPref
			if candPref {
				after++
			}
			if after < p.need && after < pref {
				return false // zou het aantal voorkeursengines onder het minimum brengen
			}
		}
		// vervang alle slechtere buren (hoogste index eerst i.v.m. swap-remove)
		sort.Sort(sort.Reverse(sort.IntSlice(near)))
		for _, i := range near {
			p.removeAt(i)
		}
		p.add(r)
		return true
	}
	if len(p.items) < p.max {
		p.add(r)
		return true
	}

	notPref := func(it result) bool { return !p.isPref(it.engine) }
	if p.prefer != 0 && candPref && pref < p.need {
		// quotum nog niet gehaald: verdring de slechtste engine zonder voorkeursbeginzet
		if w := p.worstWhere(notPref); w >= 0 {
			p.removeAt(w)
			p.add(r)
			return true
		}
	}
	w := p.worstIdx()
	if p.prefer != 0 && !candPref && pref <= p.need {
		w = p.worstWhere(notPref) // voorkeursengines mogen niet verdrongen worden
	}
	if w >= 0 && better(r, p.items[w]) {
		p.removeAt(w)
		p.add(r)
		return true
	}
	return false
}

func (p *pool) perfectCount() int {
	n := 0
	for _, it := range p.items {
		if it.losses == 0 {
			n++
		}
	}
	return n
}

// ---------- kandidaten genereren ----------
//
// Zoekruimte (zoals main.go, maar letters zijn optioneel): een engine van 12 tekens begint met 0 tot maxLetterPrefix
// letters (WVALD = vaste zet), gevolgd door dieptecijfers 1-9. Per letter geldt een maximum
// (W, V, A, L: 3, D: 1); de D-zet is hetzelfde als cijfer 5, dus samen max één keer (D of 5).

const maxLetterPrefix = 4

var letters = [5]byte{'W', 'V', 'A', 'L', 'D'}
var letterLimits = [5]int{3, 3, 3, 3, 1}

// symIdx zet een teken om naar een index 0..13 ('1'-'9' -> 0..8, W V A L D -> 9..13).
func symIdx(c byte) int {
	if c >= '1' && c <= '9' {
		return int(c - '1')
	}
	switch c {
	case 'W':
		return 9
	case 'V':
		return 10
	case 'A':
		return 11
	case 'L':
		return 12
	}
	return 13 // D
}

// validSearch controleert of een engine binnen de zoekruimte valt.
func validSearch(e string) bool {
	if len(e) != 12 {
		return false
	}
	k := 0
	for k < 12 && isMoveLetter(e[k]) {
		k++
	}
	if k > maxLetterPrefix {
		return false
	}
	var cnt [5]int
	for i := 0; i < k; i++ {
		idx := moveToIndexArray[e[i]]
		cnt[idx]++
		if cnt[idx] > letterLimits[idx] {
			return false
		}
	}
	fives := cnt[4] // D-letter telt als 5
	for i := k; i < 12; i++ {
		if e[i] < '1' || e[i] > '9' || (i == 0 && e[i] > '5') { // eerste zet als cijfer: alleen 1-5
			return false
		}
		if e[i] == '5' {
			fives++
		}
	}
	return fives <= 1
}

// weight: hoe zeldzamer een teken op die positie in de pool, hoe groter het gewicht.
// De eerste zetten (prefixLen) spreiden sterker (1/c^3) dan de rest (1/c).
func (p *pool) weight(pos int, c byte) float64 {
	n := float64(p.counts[pos][symIdx(c)]) + 1
	if pos < prefixLen {
		return 1 / (n * n * n)
	}
	return 1 / n
}

// pick kiest uit options volgens de gewichten.
func pick(options []byte, w []float64, rng *rand.Rand) byte {
	total := 0.0
	for _, x := range w {
		total += x
	}
	x := rng.Float64() * total
	for i, wi := range w {
		x -= wi
		if x <= 0 {
			return options[i]
		}
	}
	return options[len(options)-1]
}

// randomCandidate bouwt een geldige engine: eerst een letter-voorvoegsel, dan cijfers.
// force (W/V/A/L/D, of 0) dwingt de beginzet af.
func (p *pool) randomCandidate(rng *rand.Rand, force byte) string {
	p.mu.Lock()
	defer p.mu.Unlock()

	// lengte van het letter-voorvoegsel: 0 = alleen cijfers (eerste zet 1-5), anders 1-4 letters
	k := 0
	switch r := rng.Intn(100); {
	case r >= 87:
		k = 4
	case r >= 70:
		k = 3
	case r >= 50:
		k = 2
	case r >= 25:
		k = 1
	}

	// de te vermijden diepte wordt in 80% van de kandidaten helemaal overgeslagen
	strict := avoidDigit != 0 && rng.Intn(100) < 80
	if force != 0 && k == 0 && avoidDigit == byte('1'+moveToIndexArray[force]) {
		k = 1 // het gelijke cijfer is de te vermijden diepte: gebruik de letter
	}

	var buf [12]byte
	var cnt [5]int
	for pos := 0; pos < k; pos++ {
		var opts []byte
		var w []float64
		for i, c := range letters {
			if cnt[i] < letterLimits[i] {
				opts = append(opts, c)
				w = append(w, p.weight(pos, c))
			}
		}
		c := pick(opts, w, rng)
		if pos == 0 && force != 0 {
			c = force
		}
		cnt[moveToIndexArray[c]]++
		buf[pos] = c
	}
	usedFive := cnt[4] > 0
	for pos := k; pos < 12; pos++ {
		var opts []byte
		var w []float64
		maxD := byte('9')
		if pos == 0 {
			maxD = '5' // eerste zet als cijfer: alleen 1-5
		}
		for d := byte('1'); d <= maxD; d++ {
			if d == '5' && usedFive {
				continue
			}
			if strict && d == avoidDigit {
				continue
			}
			opts = append(opts, d)
			w = append(w, p.weight(pos, d))
		}
		c := pick(opts, w, rng)
		if pos == 0 && force != 0 {
			c = byte('1' + moveToIndexArray[force]) // W=1, V=2, A=3, L=4, D=5
		}
		if c == '5' {
			usedFive = true
		}
		buf[pos] = c
	}
	return string(buf[:])
}

// mutate verandert k posities van een bestaande engine en laat soms het letter-voorvoegsel
// korter of langer worden. Het resultaat is altijd een geldige engine.
func mutate(src string, k int, rng *rand.Rand) string {
	cur := src
	for n := 0; n < k; n++ {
		for try := 0; try < 30; try++ {
			b := []byte(cur)
			lk := 0
			for lk < 12 && isMoveLetter(b[lk]) {
				lk++
			}
			if rng.Intn(100) < 15 {
				// voorvoegsel langer (cijfer -> letter) of korter (letter -> cijfer)
				if rng.Intn(2) == 0 && lk < maxLetterPrefix {
					b[lk] = letters[rng.Intn(5)]
				} else if lk > 0 {
					b[lk-1] = randDigit(rng)
				}
			} else {
				pos := rng.Intn(12)
				if n < 2 {
					pos = rng.Intn(prefixLen) // minstens 2 wijzigingen in de eerste zetten
				}
				if pos < lk {
					b[pos] = letters[rng.Intn(5)]
				} else {
					b[pos] = randDigit(rng)
				}
			}
			if s := string(b); s != cur && validSearch(s) {
				cur = s
				break
			}
		}
	}
	return cur
}

func (p *pool) pickParent(rng *rand.Rand) (string, bool) {
	p.mu.Lock()
	defer p.mu.Unlock()
	if len(p.items) == 0 {
		return "", false
	}
	// bij voorkeur een ouder zonder verliezen
	for try := 0; try < 8; try++ {
		it := p.items[rng.Intn(len(p.items))]
		if it.losses == 0 {
			return it.engine, true
		}
	}
	return p.items[rng.Intn(len(p.items))].engine, true
}

// ---------- invoer ----------

func parseEngineCode(input string) string {
	parts := strings.Split(input, ":")
	engine := strings.TrimSpace(input)
	if len(parts) > 2 {
		engine = strings.TrimSpace(parts[2])
	}
	if isFixed13 := len(engine) == 13 && strings.Trim(engine, "WVALD") == ""; len(engine) > 12 && !isFixed13 {
		return engine[:12]
	}
	return engine
}

// Vaste instellingen (niet door de gebruiker aan te passen)
const stallTime = 1500 * time.Millisecond // zo lang geen vooruitgang -> voorkeursquotum omlaag

const (
	maxSeconds    = 30 // maximale zoektijd per level
	minDist       = 3  // minimaal verschil (van 12 posities) tussen twee pool-engines
	preDist       = 3  // minimaal verschil binnen de eerste prefixLen zetten
	mutatePercent = 30 // % kandidaten dat een mutatie van een pool-engine is
	defaultOutput = 13 // standaard aantal engines per level
	namePrefix    = "L"
	outputFile    = "ketting_engines.txt"
	boteFile      = "bote.txt"
	eloMultiplier = 75  // rating per level
	eloStart      = 425 // rating-offset: level L begint op (L-1)*75+425
)

// levelEngine is een engine met zijn level en naam, zoals in het protocolformaat Naam:level:code.
type levelEngine struct {
	name  string
	level int
	code  string
}

// parseProtocolLine leest "Naam:level:code". Het level is verplicht.
func parseProtocolLine(line string) (levelEngine, error) {
	parts := strings.Split(line, ":")
	if len(parts) < 3 {
		return levelEngine{}, fmt.Errorf("formaat moet Naam:level:code zijn")
	}
	lv, err := strconv.Atoi(strings.TrimSpace(parts[1]))
	if err != nil || lv < 1 {
		return levelEngine{}, fmt.Errorf("ongeldig level '%s'", strings.TrimSpace(parts[1]))
	}
	e := parseEngineCode(line)
	validDepth := isValidDepthCode(e)
	validFixed := len(e) == 13 && strings.Trim(e, "WVALD") == ""
	if !validDepth && !validFixed {
		return levelEngine{}, fmt.Errorf("ongeldige engine code '%s'", e)
	}
	return levelEngine{name: strings.TrimSpace(parts[0]), level: lv, code: e}, nil
}

// readLevelEngines leest engines tot '.' of een lege regel.
func readLevelEngines(sc *bufio.Scanner) []levelEngine {
	var out []levelEngine
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())
		if line == "." || line == "" {
			break
		}
		e, err := parseProtocolLine(line)
		if err != nil {
			fmt.Printf("Regel '%s' overgeslagen: %v\n", line, err)
			continue
		}
		out = append(out, e)
	}
	return out
}

// opponentsFor geeft de codes van de twee hoogste levels onder `below` (en niet hoger).
func opponentsFor(all []levelEngine) (codes []string, levels []int) {
	max := 0
	for _, e := range all {
		if e.level > max {
			max = e.level
		}
	}
	for _, e := range all {
		if e.level == max || e.level == max-1 {
			codes = append(codes, e.code)
		}
	}
	if max > 1 {
		levels = []int{max - 1, max}
	} else {
		levels = []int{max}
	}
	return
}

// search zoekt `size` engines die zo goed mogelijk scoren tegen de tegenstanders.
func search(opponents []string, size int, prefer byte, avoid byte) *pool {
	avoidDigit = avoid
	p := &pool{max: size, minDist: minDist, preDist: preDist, prefer: prefer, need: (size + 1) / 2}
	threads := runtime.NumCPU()
	var evaluated int64
	var stop int32
	start := time.Now()
	deadline := start.Add(maxSeconds * time.Second)

	var wg sync.WaitGroup
	for t := 0; t < threads; t++ {
		wg.Add(1)
		go func(seed int64) {
			defer wg.Done()
			rng := rand.New(rand.NewSource(seed))
			for atomic.LoadInt32(&stop) == 0 {
				var force byte // een deel van de kandidaten dwingt de voorkeursbeginzet af
				if prefer != 0 && rng.Intn(2) == 0 {
					force = prefer
				}
				var cand string
				if rng.Intn(100) < mutatePercent {
					if parent, ok := p.pickParent(rng); ok {
						cand = mutate(parent, preDist+rng.Intn(3), rng)
					}
					if force != 0 && cand != "" && firstMove(cand) != force {
						cand = ""
					}
				}
				if cand == "" {
					cand = p.randomCandidate(rng, force)
				}
				r := evaluate(cand, opponents)
				atomic.AddInt64(&evaluated, 1)
				p.offer(r)
			}
		}(time.Now().UnixNano() + int64(t)*7919)
	}

	// stop zodra de pool vol is met engines zonder verlies, of na maxSeconds
	ticker := time.NewTicker(250 * time.Millisecond)
	minNeed := (size + 2) / 3 // ondergrens voor het aantal engines met de voorkeursbeginzet
	lastPerfect, lastChange := -1, time.Now()
	lastAvoid, lastAvoidChange := -1, time.Now()
	for range ticker.C {
		p.mu.Lock()
		n, perfect, pref := len(p.items), p.perfectCount(), p.prefCount()
		// geen vooruitgang meer in het aantal engines zonder verlies: voorkeursquotum 1 omlaag
		if perfect != lastPerfect {
			lastPerfect, lastChange = perfect, time.Now()
		} else if prefer != 0 && perfect < size && p.need > minNeed && time.Since(lastChange) > stallTime {
			p.need-- // alles winnen lukt niet met dit quotum: 1 engine minder met de voorkeursbeginzet
			lastChange = time.Now()
		}
		need := p.need
		if prefer == 0 {
			need = 0 // geen voorkeursbeginzet: geen quotum
		}
		asum := 0
		for _, it := range p.items {
			asum += it.avoid
		}
		if asum != lastAvoid {
			lastAvoid, lastAvoidChange = asum, time.Now()
		}
		p.mu.Unlock()
		fmt.Printf("\r  [%4.1fs] pool %d/%d, %d zonder verlies   ", time.Since(start).Seconds(), n, size, perfect)
		if (perfect >= size && pref >= need && (avoid == 0 || asum == 0 || time.Since(lastAvoidChange) > stallTime)) || time.Now().After(deadline) {
			break
		}
	}
	ticker.Stop()
	atomic.StoreInt32(&stop, 1)
	wg.Wait()
	fmt.Printf("\r  %d kandidaten getest in %.1fs%40s\n", evaluated, time.Since(start).Seconds(), "")

	sort.Slice(p.items, func(i, j int) bool { return better(p.items[i], p.items[j]) })
	return p
}

// levelBlock geeft de regels van één level, in volgorde 01..N.
func levelBlock(level int, p *pool) string {
	var sb strings.Builder
	for i, it := range p.items {
		fmt.Fprintf(&sb, "%s%d-%02d:%d:%s\n", namePrefix, level, i+1, level, it.engine)
	}
	return sb.String()
}

// boteRating geeft de rating van engine idx (0 = engine 01) van n engines in een level.
// Level L loopt van (L-1)*75+425 tot L*75+425; engine 01 krijgt 1 minder dan dat maximum,
// de rest zakt in gelijke stappen van 75/n (afgerond, dus afwisselend 5 en 6 bij n=13).
func boteRating(level, idx, n int) int {
	top := level*eloMultiplier + eloStart - 1
	return top - int(math.Round(float64(idx*eloMultiplier)/float64(n)))
}

// boteBlock geeft de regels van één level voor bote.txt: "Naam   level   rating".
func boteBlock(level int, p *pool) string {
	var sb strings.Builder
	for i := range p.items {
		fmt.Fprintf(&sb, "%s%d-%02d   %d   %d\n", namePrefix, level, i+1, level, boteRating(level, i, len(p.items)))
	}
	return sb.String()
}

// writeAll schrijft alle levels, hoogste level bovenaan (blocks staan van laag naar hoog).
func writeAll(blocks, boteBlocks []string) error {
	var sb, bb strings.Builder
	for i := len(blocks) - 1; i >= 0; i-- {
		sb.WriteString(blocks[i])
		bb.WriteString(boteBlocks[i])
	}
	if err := os.WriteFile(outputFile, []byte(sb.String()), 0644); err != nil {
		return err
	}
	return os.WriteFile(boteFile, []byte(bb.String()), 0644)
}

func askInt(sc *bufio.Scanner, prompt string, def, min, max int) (int, bool) {
	for {
		fmt.Print(prompt)
		if !sc.Scan() {
			return 0, false
		}
		txt := strings.TrimSpace(sc.Text())
		if txt == "" && def > 0 {
			return def, true
		}
		if n, err := strconv.Atoi(txt); err == nil && n >= min && n <= max {
			return n, true
		}
		fmt.Println("Ongeldige invoer.")
	}
}

func main() {
	sc := bufio.NewScanner(os.Stdin)
	sc.Buffer(make([]byte, 1024*1024), 1024*1024)

	for {
		fmt.Println("Voer engines in met formaat Naam:level:code (één per regel, '.' of lege regel om te stoppen):")
		all := readLevelEngines(sc)
		if len(all) == 0 {
			fmt.Println("Geen engines ingevoerd. Gestopt.")
			return
		}
		maxLevel := 0
		for _, e := range all {
			if e.level > maxLevel {
				maxLevel = e.level
			}
		}

		endLevel, ok := askInt(sc, fmt.Sprintf("Eindlevel? (hoger dan %d): ", maxLevel), 0, maxLevel+1, 100000)
		if !ok {
			return
		}
		size, ok := askInt(sc, fmt.Sprintf("Hoeveel engines per level? (default %d): ", defaultOutput), defaultOutput, 1, 10000)
		if !ok {
			return
		}

		prefer := askPrefer(sc) // eenmalig voor de hele keten
		if prefer != 0 {
			fmt.Printf("Voorkeursbeginzet %c: streven naar %d van de %d engines per level (zakt zo nodig naar minimaal %d).\n", prefer, (size+1)/2, size, (size+2)/3)
		}

		avoid := askAvoid(sc) // eenmalig voor de hele keten
		if avoid != 0 {
			fmt.Printf("Diepte %c wordt zo weinig mogelijk gespeeld (mag wel, maar liever niet).\n", avoid)
		}

		var blocks, boteBlocks []string

		for level := maxLevel + 1; level <= endLevel; level++ {
			opponents, lvls := opponentsFor(all)
			fmt.Printf("Level %d: %d tegenstanders (level %v), zoeken naar %d engines (max %ds)...\n",
				level, len(opponents), lvls, size, maxSeconds)
			p := search(opponents, size, prefer, avoid)
			if len(p.items) == 0 {
				fmt.Printf("Geen engines gevonden voor level %d, ketting gestopt.\n", level)
				break
			}

			losses := map[int]int{}
			for i, it := range p.items {
				losses[it.losses]++
				all = append(all, levelEngine{name: fmt.Sprintf("%s%d-%02d", namePrefix, level, i+1), level: level, code: it.engine})
			}
			var keys []int
			for k := range losses {
				keys = append(keys, k)
			}
			sort.Ints(keys)
			summary := ""
			for _, k := range keys {
				summary += fmt.Sprintf(" %dx met %d verlies", losses[k], k)
			}
			fmt.Printf("  level %d: %d engines,%s\n", level, len(p.items), summary)
			if prefer != 0 {
				fmt.Printf("  %d engines beginnen met %c (quotum %d)\n", p.prefCount(), prefer, p.need)
			}

			if avoid != 0 {
				n, total := 0, 0
				for _, it := range p.items {
					total += it.avoid
					if it.avoid == 0 {
						n++
					}
				}
				fmt.Printf("  %d van de %d engines spelen diepte %c nooit (in totaal %d keer)\n", n, len(p.items), avoid, total)
			}
			blocks = append(blocks, levelBlock(level, p))
			boteBlocks = append(boteBlocks, boteBlock(level, p))
			// na elk level opslaan, zodat een onderbreking niets kost
			if err := writeAll(blocks, boteBlocks); err != nil {
				fmt.Println("Fout bij het schrijven:", err)
				break
			}
		}
		fmt.Printf("Klaar. Opgeslagen in %s en %s\n\n", outputFile, boteFile)
	}
}

func isMoveLetter(c byte) bool {
	return c == 'W' || c == 'V' || c == 'A' || c == 'L' || c == 'D'
}

// isValidDepthCode aanvaardt 12 tekens: eerst letters (WVALD, vaste zet), dan cijfers (1-9, diepte).
// bv. AVAWD6161164: speelt eerst A,V,A,W,D en daarna de dieptes 6,1,6,1,1,6,4.
func isValidDepthCode(engine string) bool {
	if len(engine) != 12 {
		return false
	}
	seenDigit := false
	for i := 0; i < len(engine); i++ {
		c := engine[i]
		switch {
		case c >= '1' && c <= '9':
			seenDigit = true
		case isMoveLetter(c):
			if seenDigit {
				return false
			}
		default:
			return false
		}
	}
	return true
}

// askPrefer vraagt de voorkeursbeginzet: W, V, A, L of D. Leeg (of ongeldig) = geen voorkeur.
func askPrefer(sc *bufio.Scanner) byte {
	fmt.Print("Voorkeur beginzet? (W/V/A/L/D, leeg = geen): ")
	if !sc.Scan() {
		return 0
	}
	txt := strings.ToUpper(strings.TrimSpace(sc.Text()))
	if txt == "" {
		return 0
	}
	if len(txt) == 1 && isMoveLetter(txt[0]) {
		return txt[0]
	}
	fmt.Println("Ongeldige invoer, geen voorkeur.")
	return 0
}

// randDigit kiest een cijfer 1-9; de te vermijden diepte wordt meestal overgeslagen.
func randDigit(rng *rand.Rand) byte {
	for {
		d := byte('1' + rng.Intn(9))
		if avoidDigit == 0 || d != avoidDigit || rng.Intn(100) >= 80 {
			return d
		}
	}
}

// askAvoid vraagt welke diepte (1-9) zo weinig mogelijk gespeeld mag worden. Leeg = geen.
func askAvoid(sc *bufio.Scanner) byte {
	fmt.Print("Vermijd welke diepte? (1-9, leeg = geen): ")
	if !sc.Scan() {
		return 0
	}
	txt := strings.TrimSpace(sc.Text())
	if txt == "" {
		return 0
	}
	if len(txt) == 1 && txt[0] >= '1' && txt[0] <= '9' {
		return txt[0]
	}
	fmt.Println("Ongeldige invoer, geen diepte vermeden.")
	return 0
}
