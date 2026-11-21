import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2115 : checkSingleBlackFast2 (-85, -61) 15719 .west (29, 40) (-59, 21) = true := by
  decide +kernel

end LangtonsAnt
