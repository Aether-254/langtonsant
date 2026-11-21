import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0534 : checkSingleBlackFast (1, -8) 5332 .north (-2, 0) (-16, -10) = true := by
  decide +kernel

end LangtonsAnt
