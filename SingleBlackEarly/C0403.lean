import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0403 : checkSingleBlack (14, -5) 15856 .south (-9, -2) (-29, -8) = true := by
  decide +kernel

end LangtonsAnt
