import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0888 : checkSingleBlack (-8, -3) 45688 .south (-32, -10) (-56, -20) = true := by
  decide +kernel

end LangtonsAnt
