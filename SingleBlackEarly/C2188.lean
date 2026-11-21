import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2188 : checkSingleBlackFast2 (-88, -68) 17484 .north (39, 29) (-65, -45) = true := by
  decide +kernel

end LangtonsAnt
