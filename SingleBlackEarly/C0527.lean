import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0527 : checkSingleBlackFast2 (-1, -6) 14628 .south (-9, -4) (-23, -18) = true := by
  decide +kernel

end LangtonsAnt
