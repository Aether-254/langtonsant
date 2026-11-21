import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0519 : checkSingleBlackFast (-5, -7) 12672 .north (-3, 5) (1, -25) = true := by
  decide +kernel

end LangtonsAnt
