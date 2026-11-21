import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1540 : checkSingleBlackFast2 (-32, -8) 12955 .west (3, 13) (-32, -7) = true := by
  decide +kernel

end LangtonsAnt
