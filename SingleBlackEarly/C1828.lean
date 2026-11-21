import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1828 : checkSingleBlackFast (-59, -36) 19541 .east (27, 12) (4, -46) = true := by
  decide +kernel

end LangtonsAnt
