import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0754 : checkSingleBlack (24, -12) 14491 .east (-7, 0) (-21, -23) = true := by
  decide +kernel

end LangtonsAnt
