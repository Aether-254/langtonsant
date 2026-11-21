import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0641 : checkSingleBlackFast (8, -10) 10516 .north (-3, -5) (-27, -3) = true := by
  decide +kernel

end LangtonsAnt
