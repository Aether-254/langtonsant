import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1425 : checkSingleBlackFast2 (-23, 5) 15649 .east (-1, -13) (-33, -18) = true := by
  decide +kernel

end LangtonsAnt
