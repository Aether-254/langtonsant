import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2101 : checkSingleBlackFast (-79, -61) 13568 .north (29, 21) (-55, -37) = true := by
  decide +kernel

end LangtonsAnt
