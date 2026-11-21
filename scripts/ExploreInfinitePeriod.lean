import InfiniteObstacleHighway

open LangtonsAnt

def main : IO Unit := do
  let mut s := chainCollisionSeed
  let mut word : Array Bool := #[]
  for _ in [:548] do
    word := word.push (decide (s.pos ∈ s.black))
    s := s.step
  let mut firstWitnesses : Array Nat := #[]
  let mut longestWitness := 0
  for q in [1:548] do
    let mut found := false
    for j in [:548] do
      if !found && word[j]! != word[(j + q) % 548]! then
        found := true
        firstWitnesses := firstWitnesses.push j
        longestWitness := max longestWitness j
    if !found then IO.println s!"short period={q}"
  IO.println s!"excluded={firstWitnesses.size}; maximum first witness={longestWitness}"
  IO.println s!"q=137 witness={firstWitnesses[136]!}, q=274 witness={firstWitnesses[273]!}"
