import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0035 : checkSingleBlack (-1, 2) 47140 .south (-1, -6) (1, -42) = true := by
  decide +kernel

end LangtonsAnt
