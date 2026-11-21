import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1695 : checkSingleBlackFast (-46, -24) 28181 .east (10, -5) (-39, -5) = true := by
  decide +kernel

end LangtonsAnt
