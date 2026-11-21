import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1616 : checkSingleBlack (-36, -16) 14780 .north (13, 3) (-39, -19) = true := by
  decide +kernel

end LangtonsAnt
