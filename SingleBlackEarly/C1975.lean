import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1975 : checkSingleBlackFast2 (-73, -45) 25425 .east (32, 20) (10, -55) = true := by
  decide +kernel

end LangtonsAnt
