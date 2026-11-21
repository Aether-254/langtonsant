import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0243 : checkSingleBlackFast (-5, -1) 10680 .north (-8, 4) (2, -20) = true := by
  decide +kernel

end LangtonsAnt
