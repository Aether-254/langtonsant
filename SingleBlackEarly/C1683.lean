import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1683 : checkSingleBlackFast (-41, -23) 11592 .north (10, 2) (-36, -18) = true := by
  decide +kernel

end LangtonsAnt
