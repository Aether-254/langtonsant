import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1710 : checkSingleBlackFast2 (-49, -22) 18210 .north (16, 9) (-43, -22) = true := by
  decide +kernel

end LangtonsAnt
