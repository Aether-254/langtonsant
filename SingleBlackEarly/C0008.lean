import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0008 : checkSingleBlackFast (-2, -1) 2714 .north (5, 5) (-14, -8) = true := by
  decide +kernel

end LangtonsAnt
