import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0609 : checkSingleBlackFast (15, 16) 8436 .north (-8, 5) (0, -21) = true := by
  decide +kernel

end LangtonsAnt
