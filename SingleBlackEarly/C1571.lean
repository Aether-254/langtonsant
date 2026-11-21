import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1571 : checkSingleBlackFast2 (-33, -14) 18974 .north (8, 9) (-31, -20) = true := by
  decide +kernel

end LangtonsAnt
