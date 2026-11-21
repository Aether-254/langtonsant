import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0429 : checkSingleBlackFast (18, 3) 9233 .east (2, -7) (-25, -19) = true := by
  decide +kernel

end LangtonsAnt
