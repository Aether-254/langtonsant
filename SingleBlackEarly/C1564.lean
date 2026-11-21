import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1564 : checkSingleBlackFast2 (-35, -12) 18293 .east (15, 0) (-8, -34) = true := by
  decide +kernel

end LangtonsAnt
