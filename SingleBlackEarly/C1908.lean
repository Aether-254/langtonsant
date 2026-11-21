import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1908 : checkSingleBlackFast2 (-67, -40) 19146 .north (25, 18) (-52, -31) = true := by
  decide +kernel

end LangtonsAnt
