import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1244 : checkSingleBlackFast2 (15, 18) 12295 .east (-7, -1) (-20, -23) = true := by
  decide +kernel

end LangtonsAnt
