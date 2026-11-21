import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0090 : checkSingleBlack (5, 3) 14292 .south (-17, -2) (-35, -8) = true := by
  decide +kernel

end LangtonsAnt
