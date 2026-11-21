import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0290 : checkSingleBlack (14, 13) 14140 .south (-1, -20) (-9, -24) = true := by
  decide +kernel

end LangtonsAnt
