import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0850 : checkSingleBlackFast (-8, 9) 9168 .north (-2, 0) (-24, 4) = true := by
  decide +kernel

end LangtonsAnt
