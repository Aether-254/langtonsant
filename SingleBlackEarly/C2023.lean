import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2023 : checkSingleBlackFast2 (-76, -53) 15199 .west (25, 35) (-54, 15) = true := by
  decide +kernel

end LangtonsAnt
