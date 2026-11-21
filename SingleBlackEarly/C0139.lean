import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0139 : checkSingleBlackFast (8, 1) 8994 .north (6, -6) (-23, -7) = true := by
  decide +kernel

end LangtonsAnt
