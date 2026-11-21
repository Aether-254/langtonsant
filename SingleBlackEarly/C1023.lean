import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1023 : checkSingleBlackFast (-5, 20) 8701 .east (-3, -9) (-23, -16) = true := by
  decide +kernel

end LangtonsAnt
