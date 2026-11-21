import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1316 : checkSingleBlack (-11, 15) 14220 .north (-1, 5) (1, -27) = true := by
  decide +kernel

end LangtonsAnt
