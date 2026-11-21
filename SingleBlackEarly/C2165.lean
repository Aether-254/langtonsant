import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2165 : checkSingleBlackFast (-87, -68) 77417 .east (47, 28) (-78, 12) = true := by
  decide +kernel

end LangtonsAnt
