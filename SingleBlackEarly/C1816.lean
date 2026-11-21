import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1816 : checkSingleBlackFast2 (-57, -31) 12308 .north (17, 9) (-43, -25) = true := by
  decide +kernel

end LangtonsAnt
