import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0480 : checkSingleBlackFast (9, 15) 23212 .north (-5, -7) (-29, -21) = true := by
  decide +kernel

end LangtonsAnt
