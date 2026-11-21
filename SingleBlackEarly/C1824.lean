import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1824 : checkSingleBlackFast2 (-57, -35) 15689 .west (16, 25) (-45, 5) = true := by
  decide +kernel

end LangtonsAnt
