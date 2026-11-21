import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1352 : checkSingleBlackFast2 (-16, 8) 10895 .east (-3, -7) (-26, -19) = true := by
  decide +kernel

end LangtonsAnt
