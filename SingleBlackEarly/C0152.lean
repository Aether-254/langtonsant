import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0152 : checkSingleBlackFast (1, 6) 8682 .north (9, -5) (-26, -4) = true := by
  decide +kernel

end LangtonsAnt
