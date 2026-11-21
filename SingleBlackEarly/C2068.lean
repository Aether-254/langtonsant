import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2068 : checkSingleBlackFast2 (-80, -56) 15451 .west (27, 37) (-56, 17) = true := by
  decide +kernel

end LangtonsAnt
