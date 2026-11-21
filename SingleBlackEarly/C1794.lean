import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1794 : checkSingleBlackFast2 (-55, -29) 12204 .north (16, 8) (-42, -24) = true := by
  decide +kernel

end LangtonsAnt
