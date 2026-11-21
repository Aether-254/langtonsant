import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0982 : checkSingleBlackFast (0, 19) 8031 .east (-2, -3) (-18, -18) = true := by
  decide +kernel

end LangtonsAnt
