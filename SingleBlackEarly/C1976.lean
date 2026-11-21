import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1976 : checkSingleBlackFast (-71, -46) 21479 .east (38, 17) (-8, -56) = true := by
  decide +kernel

end LangtonsAnt
