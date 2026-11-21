import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1846 : checkSingleBlackFast2 (-59, -37) 15793 .west (17, 26) (-46, 6) = true := by
  decide +kernel

end LangtonsAnt
