import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0072 : checkSingleBlackFast (3, -4) 9118 .north (9, 2) (-24, -1) = true := by
  decide +kernel

end LangtonsAnt
