import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1688 : checkSingleBlackFast (-47, -20) 29666 .north (12, -1) (-45, -30) = true := by
  decide +kernel

end LangtonsAnt
