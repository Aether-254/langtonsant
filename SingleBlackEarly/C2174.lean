import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2174 : checkSingleBlackFast (-89, -64) 22415 .east (47, 26) (1, -65) = true := by
  decide +kernel

end LangtonsAnt
