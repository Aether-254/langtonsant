import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1150 : checkSingleBlackFast2 (19, -20) 10436 .north (-1, 1) (-25, 3) = true := by
  decide +kernel

end LangtonsAnt
