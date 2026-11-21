import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0765 : checkSingleBlackFast (20, -16) 10604 .north (-3, -1) (-27, 1) = true := by
  decide +kernel

end LangtonsAnt
