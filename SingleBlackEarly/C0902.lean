import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0902 : checkSingleBlackFast2 (-10, 10) 12756 .north (-5, 3) (1, -25) = true := by
  decide +kernel

end LangtonsAnt
