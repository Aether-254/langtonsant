import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0608 : checkSingleBlackFast (14, 16) 8108 .north (-8, 7) (0, -19) = true := by
  decide +kernel

end LangtonsAnt
