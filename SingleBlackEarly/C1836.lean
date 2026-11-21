import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1836 : checkSingleBlackFast2 (-56, -36) 15820 .north (23, 13) (-49, -29) = true := by
  decide +kernel

end LangtonsAnt
