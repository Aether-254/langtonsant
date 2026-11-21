import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2139 : checkSingleBlack (-85, -65) 46722 .north (54, 37) (-81, -20) = true := by
  decide +kernel

end LangtonsAnt
