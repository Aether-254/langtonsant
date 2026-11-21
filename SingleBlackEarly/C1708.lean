import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1708 : checkSingleBlackFast2 (-48, -20) 16473 .west (17, 23) (-43, 0) = true := by
  decide +kernel

end LangtonsAnt
