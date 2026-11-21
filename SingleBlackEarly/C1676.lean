import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1676 : checkSingleBlack (-43, -22) 13922 .north (15, 3) (-42, -14) = true := by
  decide +kernel

end LangtonsAnt
