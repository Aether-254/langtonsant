import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1798 : checkSingleBlackFast2 (-57, -30) 18626 .north (20, 13) (-47, -26) = true := by
  decide +kernel

end LangtonsAnt
