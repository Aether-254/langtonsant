import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0452 : checkSingleBlackFast2 (18, 9) 17428 .north (-2, 6) (2, -24) = true := by
  decide +kernel

end LangtonsAnt
