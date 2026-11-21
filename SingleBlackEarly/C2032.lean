import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2032 : checkSingleBlackFast (-74, -56) 29291 .east (40, 28) (-1, -50) = true := by
  decide +kernel

end LangtonsAnt
