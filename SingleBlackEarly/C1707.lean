import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1707 : checkSingleBlackFast (-48, -21) 11888 .north (12, 4) (-38, -20) = true := by
  decide +kernel

end LangtonsAnt
