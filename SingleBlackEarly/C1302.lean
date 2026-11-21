import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1302 : checkSingleBlack (-9, 21) 14620 .north (-1, 3) (3, -27) = true := by
  decide +kernel

end LangtonsAnt
