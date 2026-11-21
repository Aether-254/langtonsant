import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0053 : checkSingleBlackFast (3, -3) 4218 .north (1, -1) (-14, -10) = true := by
  decide +kernel

end LangtonsAnt
