import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1718 : checkSingleBlackFast2 (-49, -26) 19021 .east (22, 7) (-1, -41) = true := by
  decide +kernel

end LangtonsAnt
