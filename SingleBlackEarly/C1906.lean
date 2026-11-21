import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1906 : checkSingleBlackFast2 (-66, -38) 17409 .west (26, 32) (-52, 9) = true := by
  decide +kernel

end LangtonsAnt
