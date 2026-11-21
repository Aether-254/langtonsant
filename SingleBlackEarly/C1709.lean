import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1709 : checkSingleBlackFast (-48, -22) 12004 .north (13, 5) (-39, -21) = true := by
  decide +kernel

end LangtonsAnt
