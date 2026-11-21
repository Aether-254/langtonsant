import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1754 : checkSingleBlackFast2 (-53, -26) 18418 .north (18, 11) (-45, -24) = true := by
  decide +kernel

end LangtonsAnt
