import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1860 : checkSingleBlackFast2 (-61, -35) 12516 .north (19, 11) (-45, -27) = true := by
  decide +kernel

end LangtonsAnt
