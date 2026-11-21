import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1902 : checkSingleBlackFast2 (-62, -42) 16132 .north (26, 16) (-52, -32) = true := by
  decide +kernel

end LangtonsAnt
