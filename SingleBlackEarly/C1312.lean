import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1312 : checkSingleBlackFast2 (-9, 18) 11056 .north (-1, -3) (-25, -1) = true := by
  decide +kernel

end LangtonsAnt
