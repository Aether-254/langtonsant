import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0870 : checkSingleBlack (-8, -1) 14662 .south (-11, -2) (-28, -11) = true := by
  decide +kernel

end LangtonsAnt
