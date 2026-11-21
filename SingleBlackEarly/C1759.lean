import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1759 : checkSingleBlackFast (-52, -29) 13951 .west (13, 23) (-42, 3) = true := by
  decide +kernel

end LangtonsAnt
