import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1843 : checkSingleBlackFast (-61, -33) 24801 .east (26, 14) (4, -49) = true := by
  decide +kernel

end LangtonsAnt
