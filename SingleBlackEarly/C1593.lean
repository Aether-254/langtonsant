import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1593 : checkSingleBlackFast (-35, -16) 28525 .east (14, -1) (-39, -11) = true := by
  decide +kernel

end LangtonsAnt
