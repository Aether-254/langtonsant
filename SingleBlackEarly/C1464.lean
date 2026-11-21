import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1464 : checkSingleBlackFast2 (-25, 1) 10644 .north (1, 0) (-27, -2) = true := by
  decide +kernel

end LangtonsAnt
