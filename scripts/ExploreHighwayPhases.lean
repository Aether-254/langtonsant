import CollisionRecovery

open LangtonsAnt

def phaseRecovery (start : FiniteState) (limit : Nat) : IO Unit := do
  let mut black : Std.HashSet Point := {}
  for p in start.black do black := black.insert p
  let mut pos := start.pos
  let mut dir := start.dir
  let mut maxWeight := weight pos
  for t in [:limit + 1] do
    maxWeight := max maxWeight (weight pos)
    if black.contains pos then
      let s : FiniteState := ⟨black.toList, pos, dir⟩
      if checkEntry s then
        IO.println s!"recovery={t}, pos={repr pos}, dir={repr dir}, maxWeight={maxWeight}"
        return
    let color := black.contains pos
    dir := turn color dir
    black := if color then black.erase pos else black.insert pos
    pos := move pos dir
  IO.println s!"no recovery certificate through {limit}; maxWeight={maxWeight}"

#eval do
  let mut s := highwaySeed
  let mut visited : Std.HashSet Point := {}
  for t in [:104 * 6] do
    if 104 * 5 <= t && !(visited.contains s.pos) then
      let normalized := s.translate (10, 10)
      IO.println s!"phase={t - 520}, pos={repr normalized.pos}, weight={weight normalized.pos}, readBlack={decide (s.pos ∈ s.black)}"
      phaseRecovery { normalized with black := toggleCells normalized.black normalized.pos } 20000
    visited := visited.insert s.pos
    s := s.step
