import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1494 : checkSingleBlackFast2 (-27, -5) 16573 .west (0, 3) (-37, -9) = true := by
  decide +kernel

end LangtonsAnt
