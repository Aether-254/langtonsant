import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2024 : checkSingleBlackFast2 (-76, -52) 15243 .west (25, 35) (-54, 15) = true := by
  decide +kernel

end LangtonsAnt
