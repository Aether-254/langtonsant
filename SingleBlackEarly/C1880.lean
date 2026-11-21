import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1880 : checkSingleBlackFast2 (-60, -40) 16028 .north (25, 15) (-51, -31) = true := by
  decide +kernel

end LangtonsAnt
