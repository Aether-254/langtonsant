import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1085 : checkSingleBlackFast2 (-8, -5) 17324 .north (-5, 8) (-7, -28) = true := by
  decide +kernel

end LangtonsAnt
