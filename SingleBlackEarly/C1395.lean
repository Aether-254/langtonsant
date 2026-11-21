import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1395 : checkSingleBlackFast2 (-17, 2) 17425 .east (-4, -8) (-28, -25) = true := by
  decide +kernel

end LangtonsAnt
