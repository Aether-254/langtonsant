import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0943 : checkSingleBlackFast (20, 7) 10700 .north (-3, -2) (-27, 0) = true := by
  decide +kernel

end LangtonsAnt
