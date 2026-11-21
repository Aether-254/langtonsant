import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1924 : checkSingleBlackFast2 (-64, -44) 16236 .north (27, 17) (-53, -33) = true := by
  decide +kernel

end LangtonsAnt
