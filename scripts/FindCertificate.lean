import FiniteAnt

open LangtonsAnt

def tracePositions : Nat -> FiniteState -> List Point
  | 0, _ => []
  | n + 1, s => s.pos :: tracePositions n s.step

#eval do
  let mut black : Std.HashSet Point := {}
  let mut pos : Point := (0, 0)
  let mut dir : Direction := .north
  for _ in [:12080] do
    let color := black.contains pos
    dir := turn color dir
    black := if color then black.erase pos else black.insert pos
    pos := move pos dir
  let origin : FiniteState := ⟨black.toList, pos, dir⟩
  let relative : FiniteState := {
    black := origin.black.map (fun (p : Point) => (p.1 - origin.pos.1, p.2 - origin.pos.2))
    pos := (0, 0)
    dir := origin.dir
  }
  let positions := tracePositions 104 relative
  let cut := (positions.map weight).foldl max (-1000)
  let seed := { relative with black := relative.black.filter (fun p => weight p <= cut) }
  let finish := seed.run 104
  let drift := finish.pos
  let nextCut := cut + weight drift
  let shifted := seed.black.map (fun (p : Point) => (p.1 + drift.1, p.2 + drift.2))
  let candidates := finish.black ++ shifted
  let restart := candidates.all (fun p => weight p > nextCut ||
    (decide (p ∈ finish.black) == decide (p ∈ shifted)))
  IO.println s!"origin={repr origin.pos}, dir={repr origin.dir}, cut={cut}"
  IO.println s!"seed={repr seed}"
  IO.println s!"finish={repr finish}"
  IO.println s!"restart={restart}, candidates={candidates.length}"
