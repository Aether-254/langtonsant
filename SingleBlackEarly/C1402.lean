import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1402 : checkSingleBlackFast2 (-21, 6) 15344 .north (-2, -1) (4, -29) = true := by
  decide +kernel

end LangtonsAnt
