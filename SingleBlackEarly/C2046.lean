import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2046 : checkSingleBlackFast2 (-78, -54) 15347 .west (26, 36) (-55, 16) = true := by
  decide +kernel

end LangtonsAnt
