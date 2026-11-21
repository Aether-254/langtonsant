import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1994 : checkSingleBlackFast2 (-74, -46) 17825 .west (30, 36) (-56, 13) = true := by
  decide +kernel

end LangtonsAnt
