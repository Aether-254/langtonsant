import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2081 : checkSingleBlackFast (-82, -55) 13656 .north (29, 21) (-55, -37) = true := by
  decide +kernel

end LangtonsAnt
