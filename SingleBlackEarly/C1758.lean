import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1758 : checkSingleBlackFast2 (-51, -29) 15377 .west (13, 22) (-42, 2) = true := by
  decide +kernel

end LangtonsAnt
