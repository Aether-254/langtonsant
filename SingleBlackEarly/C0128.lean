import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0128 : checkSingleBlackFast (5, 2) 1892 .south (-4, -3) (-10, -7) = true := by
  decide +kernel

end LangtonsAnt
