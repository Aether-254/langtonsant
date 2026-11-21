import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2061 : checkSingleBlackFast (-80, -54) 13668 .north (29, 21) (-55, -37) = true := by
  decide +kernel

end LangtonsAnt
