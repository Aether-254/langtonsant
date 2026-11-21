import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1777 : checkSingleBlackFast (-55, -27) 24397 .east (23, 11) (1, -46) = true := by
  decide +kernel

end LangtonsAnt
