import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1864 : checkSingleBlackFast2 (-63, -36) 18938 .north (23, 16) (-50, -29) = true := by
  decide +kernel

end LangtonsAnt
