import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1451 : checkSingleBlackFast2 (-24, -1) 25312 .north (-4, 2) (-6, -34) = true := by
  decide +kernel

end LangtonsAnt
