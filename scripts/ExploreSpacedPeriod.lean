import InfiniteHighwayPeriod

open LangtonsAnt

def windowAt (a : Array Bool) (n width : Nat) : Array Bool :=
  (List.range width).toArray.map (fun j => a[(n + j) % a.size]!)

def occurrences (a marker : Array Bool) : Array Nat :=
  (List.range a.size).toArray.filter (fun n => windowAt a n marker.size == marker)

def main : IO Unit := do
  let c := obstacleWord
  let s := highwayWord.toArray
  let cs := c ++ s
  for width in [4:25] do
    for n in [:548 - width + 1] do
      let marker := windowAt c n width
      if occurrences c marker == #[n] && occurrences cs marker == #[n] && (occurrences s marker).isEmpty then
        let letters := String.ofList (marker.toList.map (fun b => if b then 'L' else 'R'))
        IO.println s!"width={width}, start={n}, marker={letters}"
        return
  IO.println "No marker found in the searched range"
