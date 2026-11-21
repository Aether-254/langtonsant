import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1121 : checkSingleBlackFast (24, -17) 10280 .north (0, 0) (-24, 2) = true := by
  decide +kernel

end LangtonsAnt
