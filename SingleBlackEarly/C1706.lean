import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1706 : checkSingleBlackFast2 (-47, -21) 11788 .north (12, 4) (-38, -20) = true := by
  decide +kernel

end LangtonsAnt
