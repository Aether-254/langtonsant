import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0736 : checkSingleBlackFast (17, -12) 10140 .north (1, -2) (-23, 0) = true := by
  decide +kernel

end LangtonsAnt
