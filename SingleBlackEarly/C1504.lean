import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1504 : checkSingleBlackFast (-26, -8) 30564 .north (4, 9) (-8, -37) = true := by
  decide +kernel

end LangtonsAnt
