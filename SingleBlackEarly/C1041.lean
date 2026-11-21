import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1041 : checkSingleBlackFast (-11, 2) 28943 .east (3, -8) (-35, 3) = true := by
  decide +kernel

end LangtonsAnt
