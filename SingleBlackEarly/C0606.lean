import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0606 : checkSingleBlack (16, 15) 13863 .east (-10, -12) (-27, -10) = true := by
  decide +kernel

end LangtonsAnt
