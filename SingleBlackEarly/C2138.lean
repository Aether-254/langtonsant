import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2138 : checkSingleBlackFast2 (-85, -64) 16106 .north (36, 24) (-63, -35) = true := by
  decide +kernel

end LangtonsAnt
