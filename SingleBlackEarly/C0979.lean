import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0979 : checkSingleBlackFast (0, 18) 7967 .east (-2, -3) (-18, -18) = true := by
  decide +kernel

end LangtonsAnt
