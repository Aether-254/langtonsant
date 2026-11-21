import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1780 : checkSingleBlackFast2 (-53, -31) 15481 .west (14, 23) (-43, 3) = true := by
  decide +kernel

end LangtonsAnt
