import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1304 : checkSingleBlackFast2 (-10, 19) 11153 .east (-1, -7) (-27, -22) = true := by
  decide +kernel

end LangtonsAnt
