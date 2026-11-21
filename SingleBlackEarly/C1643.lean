import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1643 : checkSingleBlackFast (-42, -16) 11692 .north (10, 2) (-36, -18) = true := by
  decide +kernel

end LangtonsAnt
