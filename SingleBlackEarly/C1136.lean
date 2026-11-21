import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1136 : checkSingleBlackFast2 (19, -17) 10572 .north (-2, 0) (-26, 2) = true := by
  decide +kernel

end LangtonsAnt
