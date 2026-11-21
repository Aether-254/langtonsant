import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1907 : checkSingleBlackFast (-66, -40) 12940 .north (22, 14) (-48, -30) = true := by
  decide +kernel

end LangtonsAnt
