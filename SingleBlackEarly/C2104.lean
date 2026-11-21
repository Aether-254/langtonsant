import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2104 : checkSingleBlackFast2 (-84, -56) 18345 .west (35, 41) (-61, 18) = true := by
  decide +kernel

end LangtonsAnt
