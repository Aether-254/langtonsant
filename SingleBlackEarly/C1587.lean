import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1587 : checkSingleBlackFast2 (-37, -13) 13223 .west (5, 16) (-35, -3) = true := by
  decide +kernel

end LangtonsAnt
