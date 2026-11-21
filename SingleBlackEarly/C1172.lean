import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1172 : checkSingleBlackFast2 (29, -18) 10480 .north (-2, 0) (-26, 2) = true := by
  decide +kernel

end LangtonsAnt
