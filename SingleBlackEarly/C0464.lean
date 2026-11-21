import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0464 : checkSingleBlack (18, 13) 14114 .south (-4, -11) (-27, -10) = true := by
  decide +kernel

end LangtonsAnt
