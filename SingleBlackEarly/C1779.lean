import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1779 : checkSingleBlackFast2 (-54, -29) 17603 .east (15, 18) (-7, -35) = true := by
  decide +kernel

end LangtonsAnt
