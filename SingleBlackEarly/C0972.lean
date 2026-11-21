import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0972 : checkSingleBlackFast (2, 16) 7959 .east (-2, -3) (-18, -18) = true := by
  decide +kernel

end LangtonsAnt
