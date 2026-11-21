import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0681 : checkSingleBlackFast (18, -10) 9892 .north (1, -2) (-23, 0) = true := by
  decide +kernel

end LangtonsAnt
