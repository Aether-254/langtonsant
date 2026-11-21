import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1692 : checkSingleBlackFast2 (-45, -23) 15065 .west (10, 19) (-39, -1) = true := by
  decide +kernel

end LangtonsAnt
