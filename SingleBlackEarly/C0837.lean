import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0837 : checkSingleBlackFast2 (5, 16) 15558 .south (-6, 3) (-29, -20) = true := by
  decide +kernel

end LangtonsAnt
