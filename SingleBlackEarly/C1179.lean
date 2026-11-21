import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1179 : checkSingleBlackFast2 (26, 0) 15036 .north (-1, 1) (-31, -3) = true := by
  decide +kernel

end LangtonsAnt
