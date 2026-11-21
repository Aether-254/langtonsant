import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2045 : checkSingleBlackFast2 (-78, -55) 15303 .west (26, 36) (-55, 16) = true := by
  decide +kernel

end LangtonsAnt
