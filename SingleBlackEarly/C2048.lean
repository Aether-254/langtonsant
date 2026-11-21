import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2048 : checkSingleBlackFast (-79, -56) 20581 .east (37, 22) (14, -56) = true := by
  decide +kernel

end LangtonsAnt
