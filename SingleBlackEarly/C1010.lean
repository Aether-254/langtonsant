import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1010 : checkSingleBlackFast2 (-12, 7) 11167 .east (-3, -7) (-26, -19) = true := by
  decide +kernel

end LangtonsAnt
