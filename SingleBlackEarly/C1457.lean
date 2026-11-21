import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1457 : checkSingleBlackFast (-23, -3) 22705 .east (-4, -12) (-32, -19) = true := by
  decide +kernel

end LangtonsAnt
