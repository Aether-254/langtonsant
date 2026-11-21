import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1479 : checkSingleBlackFast2 (-25, -5) 16000 .north (11, 5) (-37, -15) = true := by
  decide +kernel

end LangtonsAnt
