import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0265 : checkSingleBlackFast2 (13, 8) 17465 .east (-4, -2) (-28, -11) = true := by
  decide +kernel

end LangtonsAnt
