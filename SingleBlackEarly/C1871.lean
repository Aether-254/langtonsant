import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1871 : checkSingleBlackFast2 (-62, -40) 19027 .east (21, 15) (-12, -33) = true := by
  decide +kernel

end LangtonsAnt
