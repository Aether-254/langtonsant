import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0222 : checkSingleBlackFast (10, 9) 1991 .east (-3, -9) (-12, -1) = true := by
  decide +kernel

end LangtonsAnt
