import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0614 : checkSingleBlackFast (4, -7) 6564 .south (-15, -3) (-21, -1) = true := by
  decide +kernel

end LangtonsAnt
