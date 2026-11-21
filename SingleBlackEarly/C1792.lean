import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1792 : checkSingleBlackFast2 (-52, -32) 15612 .north (21, 11) (-47, -27) = true := by
  decide +kernel

end LangtonsAnt
