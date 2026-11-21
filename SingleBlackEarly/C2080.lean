import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2080 : checkSingleBlack (-81, -55) 13556 .north (29, 21) (-55, -37) = true := by
  decide +kernel

end LangtonsAnt
