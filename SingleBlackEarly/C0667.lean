import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0667 : checkSingleBlackFast (12, -8) 10164 .north (1, -1) (-23, 1) = true := by
  decide +kernel

end LangtonsAnt
