import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0176 : checkSingleBlackFast2 (-8, 5) 12522 .south (-1, 3) (-24, -14) = true := by
  decide +kernel

end LangtonsAnt
