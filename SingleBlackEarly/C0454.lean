import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0454 : checkSingleBlack (19, 10) 11119 .east (-14, -11) (-20, -22) = true := by
  decide +kernel

end LangtonsAnt
