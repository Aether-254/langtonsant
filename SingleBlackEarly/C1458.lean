import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1458 : checkSingleBlackFast (-24, -3) 23364 .south (-1, -8) (-17, -22) = true := by
  decide +kernel

end LangtonsAnt
