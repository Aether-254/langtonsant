import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0707 : checkSingleBlackFast (0, -9) 10812 .north (-3, -2) (-27, 0) = true := by
  decide +kernel

end LangtonsAnt
