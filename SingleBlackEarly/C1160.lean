import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1160 : checkSingleBlackFast (27, -15) 10378 .north (-8, 8) (-5, -21) = true := by
  decide +kernel

end LangtonsAnt
