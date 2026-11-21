import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0371 : checkSingleBlackFast (12, -3) 5052 .north (-2, 0) (-16, -10) = true := by
  decide +kernel

end LangtonsAnt
