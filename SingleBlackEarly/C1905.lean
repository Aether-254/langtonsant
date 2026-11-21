import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1905 : checkSingleBlackFast2 (-66, -39) 12824 .north (21, 13) (-47, -29) = true := by
  decide +kernel

end LangtonsAnt
