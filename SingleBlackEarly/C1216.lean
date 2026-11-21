import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1216 : checkSingleBlackFast2 (23, 10) 10583 .east (-3, -1) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
