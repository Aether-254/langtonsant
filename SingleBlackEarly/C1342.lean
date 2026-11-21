import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1342 : checkSingleBlackFast2 (-15, 12) 15116 .north (-9, 3) (-3, -25) = true := by
  decide +kernel

end LangtonsAnt
