import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1454 : checkSingleBlack (-25, -2) 14211 .east (9, -8) (-27, -9) = true := by
  decide +kernel

end LangtonsAnt
