import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0211 : checkSingleBlackFast (7, 4) 3473 .east (-8, -8) (-12, -5) = true := by
  decide +kernel

end LangtonsAnt
