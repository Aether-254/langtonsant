import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0515 : checkSingleBlackFast (-6, -6) 6548 .north (2, 2) (-18, -14) = true := by
  decide +kernel

end LangtonsAnt
