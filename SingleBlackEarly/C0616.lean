import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0616 : checkSingleBlackFast2 (3, -8) 12754 .north (-4, 0) (-19, -17) = true := by
  decide +kernel

end LangtonsAnt
