import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0224 : checkSingleBlackFast (8, 10) 3676 .south (-9, -8) (-15, -10) = true := by
  decide +kernel

end LangtonsAnt
