import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1329 : checkSingleBlackFast2 (-14, 16) 19010 .north (6, -8) (-33, -15) = true := by
  decide +kernel

end LangtonsAnt
