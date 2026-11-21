import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1417 : checkSingleBlackFast2 (-19, 0) 19156 .north (-7, 2) (-3, -28) = true := by
  decide +kernel

end LangtonsAnt
