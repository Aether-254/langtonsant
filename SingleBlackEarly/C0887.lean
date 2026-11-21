import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0887 : checkSingleBlackFast (-10, -3) 10154 .north (0, 2) (-23, -17) = true := by
  decide +kernel

end LangtonsAnt
