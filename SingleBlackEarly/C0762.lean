import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0762 : checkSingleBlackFast (16, -15) 8712 .north (-6, 8) (-4, -18) = true := by
  decide +kernel

end LangtonsAnt
