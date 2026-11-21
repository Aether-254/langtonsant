import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1547 : checkSingleBlackFast2 (-30, -11) 19360 .north (17, 13) (-43, -5) = true := by
  decide +kernel

end LangtonsAnt
