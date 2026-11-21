import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0772 : checkSingleBlackFast (22, -16) 10336 .north (-2, -2) (-26, 0) = true := by
  decide +kernel

end LangtonsAnt
