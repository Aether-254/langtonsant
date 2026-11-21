import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1138 : checkSingleBlackFast2 (21, -19) 10464 .north (-1, 1) (-25, 3) = true := by
  decide +kernel

end LangtonsAnt
