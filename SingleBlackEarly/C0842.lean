import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0842 : checkSingleBlackFast2 (-2, 14) 11412 .north (-5, 5) (3, -21) = true := by
  decide +kernel

end LangtonsAnt
