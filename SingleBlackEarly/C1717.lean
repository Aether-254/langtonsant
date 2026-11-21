import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1717 : checkSingleBlackFast2 (-48, -26) 18299 .east (14, 8) (-19, -26) = true := by
  decide +kernel

end LangtonsAnt
