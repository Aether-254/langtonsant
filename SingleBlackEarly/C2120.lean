import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2120 : checkSingleBlackFast (-82, -64) 29707 .east (44, 32) (3, -54) = true := by
  decide +kernel

end LangtonsAnt
