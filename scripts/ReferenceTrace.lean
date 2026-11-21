import LangtonsAnt

open LangtonsAnt

/- A finite diagnostic, not a proof of infinite repetition. -/
def collectReads : Nat -> State -> State × List Bool
  | 0, s => (s, [])
  | n + 1, s =>
    let tail := collectReads n (step s)
    (tail.1, s.board s.pos :: tail.2)

#eval do
  let start := run blank 10000
  let first := collectReads 104 start
  let second := collectReads 104 first.1
  let drift := (first.1.pos.1 - start.pos.1, first.1.pos.2 - start.pos.2)
  IO.println s!"reference start: {repr start.pos}, {repr start.dir}"
  IO.println s!"104-step displacement: {repr drift}"
  IO.println s!"heading restored: {first.1.dir == start.dir}"
  IO.println s!"next block agrees: {first.2 == second.2}"
  IO.println (String.ofList (first.2.map (fun (black : Bool) => if black then 'L' else 'R')))
