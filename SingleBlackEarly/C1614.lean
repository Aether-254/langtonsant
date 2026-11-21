import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1614 : checkSingleBlackFast (-36, -18) 24888 .north (8, 0) (-42, -26) = true := by
  decide +kernel

end LangtonsAnt
