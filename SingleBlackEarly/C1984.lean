import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1984 : checkSingleBlackFast2 (-71, -50) 15378 .north (29, 17) (-56, -28) = true := by
  decide +kernel

end LangtonsAnt
