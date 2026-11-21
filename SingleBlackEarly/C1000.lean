import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1000 : checkSingleBlackFast2 (-9, 13) 12606 .north (1, -1) (-28, -6) = true := by
  decide +kernel

end LangtonsAnt
