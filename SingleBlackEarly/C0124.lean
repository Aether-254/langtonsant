import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0124 : checkSingleBlackFast (4, 7) 2915 .east (-6, -8) (-11, -6) = true := by
  decide +kernel

end LangtonsAnt
