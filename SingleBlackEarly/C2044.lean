import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2044 : checkSingleBlackFast2 (-77, -55) 16729 .west (26, 35) (-55, 15) = true := by
  decide +kernel

end LangtonsAnt
