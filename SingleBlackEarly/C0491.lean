import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0491 : checkSingleBlackFast2 (3, 15) 16254 .south (-14, -10) (-25, -17) = true := by
  decide +kernel

end LangtonsAnt
