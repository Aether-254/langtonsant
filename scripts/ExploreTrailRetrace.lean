import FreshCollision

open LangtonsAnt

/-! Candidate discovery only. No theorem depends on this executable. -/

namespace TrailExploration

instance : Inhabited Direction := ⟨.north⟩

structure FastState where
  black : Std.HashSet Point
  pos : Point
  dir : Direction

def ofFinite (s : FiniteState) : FastState :=
  { black := Std.HashSet.ofList s.black, pos := s.pos, dir := s.dir }

def stepFast (s : FastState) : FastState := Id.run do
  let c := s.black.contains s.pos
  let d := turn c s.dir
  return { black := if c then s.black.erase s.pos else s.black.insert s.pos
           pos := move s.pos d, dir := d }

def runFast (s : FastState) (n : Nat) : FastState := Id.run do
  let mut s := s
  for _ in [:n] do s := stepFast s
  return s

def flipped (h : Nat) : FastState := Id.run do
  let s := runFast (ofFinite highwaySeed) (104 * h + 49)
  return { s with black := if s.black.contains s.pos then s.black.erase s.pos
    else s.black.insert s.pos }

def trace (s : FastState) (n : Nat) : Array (Point × Direction × Bool) := Id.run do
  let mut out := #[]
  let mut s := s
  for _ in [:n+1] do
    out := out.push (s.pos, s.dir, s.black.contains s.pos)
    s := stepFast s
  return out

def difference (s t : FastState) : List Point :=
  s.black.toList.filter (fun p => !t.black.contains p) ++
    t.black.toList.filter (fun p => !s.black.contains p)

def main : IO Unit := do
  let h := 100
  let a := trace (flipped h) 62000
  for period in [4,8,12,16,24,52,104,208,312,416] do
    let mut streak := 0
    let mut best := 0
    let mut bestStart := 0
    let mut drift : Point := (0,0)
    let mut bestDrift : Point := (0,0)
    for j in [:a.size-period] do
      let x := a[j]!
      let y := a[j+period]!
      let delta := subPoint y.1 x.1
      if y.2 == x.2 && delta == drift then streak := streak + 1
      else
        streak := if y.2 == x.2 then 1 else 0
        drift := delta
      if streak > best then
        best := streak
        bestStart := j + 1 - streak
        bestDrift := drift
    IO.println s!"period={period} best=[{bestStart},{bestStart+best}) drift={repr bestDrift}"
  let b := trace (flipped 11) 52300
  let bounded := b.toList.take 52214
  IO.println s!"base bounds x=[{bounded.foldl (fun m z => min m z.1.1) 1000},{bounded.foldl (fun m z => max m z.1.1) (-1000)}] y=[{bounded.foldl (fun m z => min m z.1.2) 1000},{bounded.foldl (fun m z => max m z.1.2) (-1000)}]"
  let bad := bounded.filter (fun z => weight z.1 > 0 && -2 <= z.1.1-z.1.2 && z.1.1-z.1.2 <= 8)
  IO.println s!"guard violations={bad.length} sample={repr (bad.take 4)}"
  let c := trace (flipped 13) 52421
  let bad13 := c.toList.filter (fun z => weight z.1 > 0 && -2 <= z.1.1-z.1.2 && z.1.1-z.1.2 <= 8)
  IO.println s!"H13 guard violations={bad13.length} endpoint={repr c[c.size-1]!}"
  let mut firstPrefixMismatch : Option Nat := none
  let mut lastSuffixMismatch := 0
  for j in [:b.size] do
    if a[j]!.1 != addPoint (-178,-178) b[j]!.1 || a[j]!.2 != b[j]!.2 then
      if firstPrefixMismatch.isNone then firstPrefixMismatch := some j
    if a[j+104*89]!.1 != b[j]!.1 || a[j+104*89]!.2 != b[j]!.2 then
      lastSuffixMismatch := j
  IO.println s!"translated prefix first mismatch={repr firstPrefixMismatch} common suffix begins={lastSuffixMismatch+1}"
  for t in [0,10000,50000,51046,51173,51277,52213] do
    let s := runFast (flipped 11) t
    let s100 := runFast (flipped 100) t
    let translated : FastState := { s with
      black := Std.HashSet.ofList (s.black.toList.map (addPoint (-178,-178)))
      pos := addPoint (-178,-178) s.pos }
    let diff := difference translated s100
    let delta := diff.map (fun p => p.1-p.2)
    let sample := b.toList.take (min (t+1) b.size)
    let maxW := sample.foldl (fun m x => max m (weight x.1)) (-1000)
    IO.println s!"t={t} base={repr s.pos}/{repr s.dir} translatedDiff={diff.length} transverse=[{delta.foldl min 1000},{delta.foldl max (-1000)}] maxW={maxW}"
  let hist := runFast (ofFinite highwaySeed) (104*100+49)
  IO.println s!"history transverse=[{hist.black.toList.foldl (fun m p => min m (p.1-p.2)) 1000},{hist.black.toList.foldl (fun m p => max m (p.1-p.2)) (-1000)}]"
  let one := runFast (ofFinite highwaySeed) 104
  let normalOne : FastState := { one with
    black := Std.HashSet.ofList (one.black.toList.map (addPoint (2,2)))
    pos := addPoint (2,2) one.pos }
  let defects := difference normalOne (ofFinite highwaySeed)
  IO.println s!"one-block defects={repr defects}"
  for t in [51069,51173,51277,52213] do
    let s := runFast (flipped 11) t
    let normalized := (⟨s.black.toList,s.pos,s.dir⟩ : FiniteState).normalize
    let tmpl := ofFinite highwaySeed
    let diff := difference (ofFinite normalized) tmpl |>.filter (fun p => weight p <= 0)
    IO.println s!"entry t={t} mismatch={repr (diff.take 20)} count={diff.length}"
  let mut start : Option Nat := none
  for j in [:a.size - 104] do
    let x := a[j]!
    let y := a[j+104]!
    let ok := y.1 == addPoint (2,2) x.1 && y.2 == x.2
    if ok && start.isNone then start := some j
    if !ok then
      if let some lo := start then
        if j - lo >= 104 then
          IO.println s!"reverse H={h} interval=[{lo},{j}) pose={repr a[lo]!} end={repr a[j]!}"
      start := none
  for h in [0,1,2,3,4,5,10,11,12,25,50,100] do
    let delay := 52213 + 104 * (h - 11)
    let s := runFast (flipped h) delay
    let entry := checkEntry ⟨s.black.toList, s.pos, s.dir⟩
    IO.println s!"H={h} delay={delay} pose={repr s.pos}/{repr s.dir} black={s.black.size} entry={entry}"
  let base := runFast (flipped 11) 52000
  for h in [12,25,50,100] do
    let s := runFast (flipped h) (52000 + 104*(h-11))
    let diff := difference base s
    IO.println s!"endpoint H={h} pose={repr s.pos}/{repr s.dir} diffCount={diff.length} diffSample={repr (diff.take 20)} weights={repr (diff.map weight |>.foldl min 0)}/{repr (diff.map weight |>.foldl max 0)}"

end TrailExploration

def main : IO Unit := TrailExploration.main
