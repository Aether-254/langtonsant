import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1174 : checkSingleBlackFast2 (27, -18) 10488 .north (-2, 0) (-26, 2) = true := by
  decide +kernel

end LangtonsAnt
