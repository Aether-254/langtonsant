import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1689 : checkSingleBlackFast2 (-47, -19) 28205 .east (16, -2) (6, -45) = true := by
  decide +kernel

end LangtonsAnt
