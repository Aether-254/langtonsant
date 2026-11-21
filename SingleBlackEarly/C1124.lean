import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1124 : checkSingleBlackFast2 (25, -18) 10676 .north (-1, 2) (-25, 4) = true := by
  decide +kernel

end LangtonsAnt
