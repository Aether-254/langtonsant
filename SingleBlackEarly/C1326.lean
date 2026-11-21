import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1326 : checkSingleBlackFast2 (-14, 17) 16692 .north (0, 5) (2, -27) = true := by
  decide +kernel

end LangtonsAnt
