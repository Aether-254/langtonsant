import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0084 : checkSingleBlackFast2 (4, -3) 10784 .south (-13, -3) (-25, -9) = true := by
  decide +kernel

end LangtonsAnt
