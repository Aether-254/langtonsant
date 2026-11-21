import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1488 : checkSingleBlackFast2 (-28, 0) 18004 .north (3, 4) (-1, -34) = true := by
  decide +kernel

end LangtonsAnt
