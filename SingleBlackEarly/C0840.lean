import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0840 : checkSingleBlack (-2, 16) 14164 .north (-4, 4) (2, -24) = true := by
  decide +kernel

end LangtonsAnt
