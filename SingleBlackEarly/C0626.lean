import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0626 : checkSingleBlackFast (7, -7) 6560 .south (-15, -3) (-21, -1) = true := by
  decide +kernel

end LangtonsAnt
