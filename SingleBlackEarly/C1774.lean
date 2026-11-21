import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1774 : checkSingleBlackFast2 (-54, -26) 16785 .west (20, 26) (-46, 3) = true := by
  decide +kernel

end LangtonsAnt
