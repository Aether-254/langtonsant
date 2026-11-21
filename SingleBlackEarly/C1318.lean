import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1318 : checkSingleBlack (-12, 16) 10792 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
