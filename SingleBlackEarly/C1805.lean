import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1805 : checkSingleBlackFast2 (-56, -34) 18715 .east (18, 12) (-15, -30) = true := by
  decide +kernel

end LangtonsAnt
