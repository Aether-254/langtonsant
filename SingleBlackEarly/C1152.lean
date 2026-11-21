import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1152 : checkSingleBlackFast2 (18, -21) 10440 .north (-1, 1) (-25, 3) = true := by
  decide +kernel

end LangtonsAnt
