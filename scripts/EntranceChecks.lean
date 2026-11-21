import EntranceChecker

namespace LangtonsAnt

def perturbBehind : FiniteState :=
  { highwaySeed with black := (100, 100) :: highwaySeed.black }

def perturbAhead : FiniteState :=
  { highwaySeed with black := (-100, -100) :: highwaySeed.black }

-- Rotation and translation change the frame, not the validity of the certificate.
example : checkEntry ((highwaySeed.rotate .north).translate (13, -27)) = true := by decide +kernel
example : checkEntry ((highwaySeed.rotate .east).translate (13, -27)) = true := by decide +kernel
example : checkEntry ((highwaySeed.rotate .south).translate (13, -27)) = true := by decide +kernel
example : checkEntry ((highwaySeed.rotate .west).translate (13, -27)) = true := by decide +kernel

-- A far-away defect ahead must block certification even if early cycles look identical.
example : checkEntry perturbBehind = true := by decide +kernel
example : checkEntry perturbAhead = false := by decide +kernel
example : searchEntry 0 highwaySeed = some 0 := by decide +kernel
example : searchEntry 0 finiteBlank = none := by decide +kernel

end LangtonsAnt
