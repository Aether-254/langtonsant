import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0286 : checkSingleBlack (14, 12) 13062 .north (-2, -6) (-21, -19) = true := by
  decide +kernel

end LangtonsAnt
