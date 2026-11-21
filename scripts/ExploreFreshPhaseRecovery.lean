import FreshCollision

open LangtonsAnt

/-! Exploration only (not a proof dependency): for each first-visit phase, search for a
recovery entry after flipping the current cell of `highwaySeed.run (104*H + phase)`.
Candidates are re-verified in `FreshPhaseRecovery.lean` by `checkRecovery` and the kernel. -/

structure Found where
  delay : Nat
  pos : Point
  dir : Direction
  maxWeight : Int
  minWeight : Int
  minCoord : Int
  maxCoord : Int

def searchRecovery (start : FiniteState) (limit : Nat) : Option Found := Id.run do
  let mut black : Std.HashSet Point := {}
  for p in start.black do black := black.insert p
  let mut pos := start.pos
  let mut dir := start.dir
  let mut maxW := weight pos
  let mut minW := weight pos
  let mut minC := min pos.1 pos.2
  let mut maxC := max pos.1 pos.2
  for t in [:limit + 1] do
    if t > 0 && black.contains pos then
      let s : FiniteState := ⟨black.toList, pos, dir⟩
      if checkEntry s then
        return some ⟨t, pos, dir, maxW, minW, minC, maxC⟩
    maxW := max maxW (weight pos)
    minW := min minW (weight pos)
    minC := min minC (min pos.1 pos.2)
    maxC := max maxC (max pos.1 pos.2)
    let color := black.contains pos
    dir := turn color dir
    black := if color then black.erase pos else black.insert pos
    pos := move pos dir
  return none

def main : IO Unit := do
  let phases := [6, 9, 15, 22, 23, 24, 32, 33, 34, 37, 38, 39, 47, 48, 49, 52, 96]
  for phase in phases do
    let mut reported := false
    for h in [:17] do
      if reported then break
      let s := highwaySeed.run (104 * h + phase)
      let f : FiniteState := { s with black := toggleCells s.black s.pos }
      match searchRecovery f 40000 with
      | none => pure ()
      | some r =>
        let ok := r.dir == .north && r.maxWeight <= 0 && weight r.pos <= 0
        IO.println s!"phase={phase} H={h} flipW={weight s.pos} delay={r.delay} entry={repr r.pos} dir={repr r.dir} maxW={r.maxWeight} minW={r.minWeight} coords=[{r.minCoord},{r.maxCoord}] certOK={ok}"
        if ok then reported := true
    if !reported then IO.println s!"phase={phase}: no certificate candidate for H<17 within 40000 steps"
