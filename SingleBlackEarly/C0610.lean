import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0610 : checkSingleBlackFast (14, 14) 8116 .north (-8, 7) (0, -19) = true := by
  decide +kernel

end LangtonsAnt
