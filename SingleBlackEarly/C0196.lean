import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0196 : checkSingleBlackFast2 (11, 2) 11896 .north (0, -1) (-6, -17) = true := by
  decide +kernel

end LangtonsAnt
