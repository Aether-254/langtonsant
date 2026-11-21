import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1384 : checkSingleBlackFast2 (-17, 5) 10915 .east (-3, -7) (-26, -19) = true := by
  decide +kernel

end LangtonsAnt
