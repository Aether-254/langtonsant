import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1845 : checkSingleBlackFast2 (-60, -35) 17915 .east (18, 21) (-4, -38) = true := by
  decide +kernel

end LangtonsAnt
