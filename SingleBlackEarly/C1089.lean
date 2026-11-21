import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1089 : checkSingleBlackFast2 (-7, -8) 16056 .north (-5, 9) (-7, -27) = true := by
  decide +kernel

end LangtonsAnt
