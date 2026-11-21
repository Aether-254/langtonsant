import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0716 : checkSingleBlackFast (5, -13) 10172 .north (-3, -2) (-27, 0) = true := by
  decide +kernel

end LangtonsAnt
