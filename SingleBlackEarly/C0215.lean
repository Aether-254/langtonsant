import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0215 : checkSingleBlackFast (10, 7) 2629 .east (-3, -8) (-14, 0) = true := by
  decide +kernel

end LangtonsAnt
