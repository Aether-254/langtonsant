import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1884 : checkSingleBlackFast2 (-64, -36) 17305 .west (25, 31) (-51, 8) = true := by
  decide +kernel

end LangtonsAnt
