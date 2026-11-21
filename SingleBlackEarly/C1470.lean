import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1470 : checkSingleBlack (-25, 0) 12664 .north (1, 10) (-1, -26) = true := by
  decide +kernel

end LangtonsAnt
