import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1849 : checkSingleBlackFast2 (-60, -38) 18923 .east (20, 14) (-13, -32) = true := by
  decide +kernel

end LangtonsAnt
