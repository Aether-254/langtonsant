import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1756 : checkSingleBlackFast (-51, -26) 20439 .east (28, 7) (-18, -46) = true := by
  decide +kernel

end LangtonsAnt
