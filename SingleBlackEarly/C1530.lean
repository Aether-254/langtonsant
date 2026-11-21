import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1530 : checkSingleBlackFast2 (-31, -5) 10956 .north (4, 0) (-30, -8) = true := by
  decide +kernel

end LangtonsAnt
