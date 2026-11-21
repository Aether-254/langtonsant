import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1411 : checkSingleBlackFast2 (-21, 3) 18665 .east (2, -6) (-12, -31) = true := by
  decide +kernel

end LangtonsAnt
