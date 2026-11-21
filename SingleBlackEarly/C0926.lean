import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0926 : checkSingleBlack (-12, 14) 13848 .north (-4, 7) (-2, -25) = true := by
  decide +kernel

end LangtonsAnt
