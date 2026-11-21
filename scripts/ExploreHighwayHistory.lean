import CollisionRecovery

open LangtonsAnt

def inspectRecovery (start : FiniteState) (limit : Nat) : IO Unit := do
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
        IO.println s!"recovery={t}, pos={repr pos}, dir={repr dir}, maxWeight={maxWeight}, black={black.size}"
        return
    let color := black.contains pos
    dir := turn color dir
    black := if color then black.erase pos else black.insert pos
    pos := move pos dir
  IO.println s!"no recovery certificate through {limit}; maxWeight={maxWeight}"

#eval do
  for k in [:9] do
    let grown := highwaySeed.run (104 * k)
    let normalized := grown.translate (negPoint grown.pos)
    let cuts := (List.range 25).filter (fun c => checkCertificate normalized 104 (-2, -2) (Int.ofNat c))
    IO.println s!"cycles={k}, retainedBlack={normalized.black.length}, validCuts={cuts}"
    inspectRecovery { normalized with black := toggleCells normalized.black normalized.pos } 20000

#eval do
  for k in [:4] do
    let s := (highwaySeed.run (104 * k + 4)).translate (2 * Int.ofNat k, 2 * Int.ofNat k)
    IO.println s!"phase=4, cycles={k}"
    inspectRecovery { s with black := toggleCells s.black s.pos } 20000
