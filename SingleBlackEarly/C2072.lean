import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2072 : checkSingleBlackFast2 (-79, -58) 15794 .north (33, 21) (-60, -32) = true := by
  decide +kernel

end LangtonsAnt
