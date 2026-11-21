import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2154 : checkSingleBlackFast2 (-87, -65) 17249 .west (31, 40) (-60, 20) = true := by
  decide +kernel

end LangtonsAnt
