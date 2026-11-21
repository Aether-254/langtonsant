import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0932 : checkSingleBlackFast2 (-14, 11) 11768 .north (-5, 4) (3, -22) = true := by
  decide +kernel

end LangtonsAnt
