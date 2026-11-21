import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0133 : checkSingleBlackFast (6, -2) 2075 .east (5, -5) (-12, -7) = true := by
  decide +kernel

end LangtonsAnt
