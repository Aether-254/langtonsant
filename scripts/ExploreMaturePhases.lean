import FreshCollision

open LangtonsAnt

def matureRecovery (start : FiniteState) (limit : Nat) : IO Unit := do
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
  IO.println s!"no certificate through {limit}; maxWeight={maxWeight}"

def main : IO Unit := do
  for phase in [5, 6, 9, 23, 34, 66, 94, 95] do
    let s := highwaySeed.run (104 * 12 + phase)
    IO.println s!"phase={phase}, historyCycles=12"
    matureRecovery { s with black := toggleCells s.black s.pos } 30000
  let mut s := flippedPhaseFourSeed
  let mut minWeight := weight s.pos
  let mut minDiagonal : Int := 0
  for _ in [:440] do
    minWeight := min minWeight (weight s.pos)
    if s.pos.1 == s.pos.2 then minDiagonal := min minDiagonal s.pos.1
    s := s.step
  IO.println s!"phase4 recovery footprint minWeight={minWeight}, minDiagonal={minDiagonal}"
