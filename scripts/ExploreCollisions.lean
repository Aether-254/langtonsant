import EntranceChecker
import SingleFlipReduction

open LangtonsAnt

def findEntryFast (start : FiniteState) (limit : Nat) : IO Unit := do
  let mut black : Std.HashSet Point := {}
  for p in start.black do black := black.insert p
  let mut pos := start.pos
  let mut dir := start.dir
  let mut extent : Nat := 0
  let mut maxWeight : Int := weight pos
  for t in [:limit + 1] do
    extent := max extent (max pos.1.natAbs pos.2.natAbs)
    maxWeight := max maxWeight (weight pos)
    if black.contains pos then
      let s : FiniteState := ⟨black.toList, pos, dir⟩
      if checkEntry s then
        IO.println s!"entry={t}, pos={repr pos}, dir={repr dir}, extent={extent}, maxWeight={maxWeight}, black={black.size}"
        return
    let color := black.contains pos
    dir := turn color dir
    black := if color then black.erase pos else black.insert pos
    pos := move pos dir
  IO.println s!"no certificate within {limit}; extent={extent}"

#eval do
  IO.println "single initial black cell at the starting point"
  findEntryFast ⟨[(0, 0)], (0, 0), .north⟩ 20000
  IO.println "flip the standard seed under the ant"
  findEntryFast { highwaySeed with black := toggleCells highwaySeed.black highwaySeed.pos } 200000
  IO.println "single initial black cell east of the start"
  findEntryFast ⟨[(1, 0)], (0, 0), .north⟩ 200000
