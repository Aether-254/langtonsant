import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0316 : checkSingleBlack (0, 11) 14798 .south (-7, -8) (-26, -17) = true := by
  decide +kernel

end LangtonsAnt
