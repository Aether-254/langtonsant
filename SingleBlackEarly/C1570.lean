import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1570 : checkSingleBlack (-32, -14) 44396 .north (23, -3) (-57, -15) = true := by
  decide +kernel

end LangtonsAnt
