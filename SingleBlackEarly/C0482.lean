import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0482 : checkSingleBlackFast2 (8, 14) 17025 .east (-7, -10) (-30, -22) = true := by
  decide +kernel

end LangtonsAnt
