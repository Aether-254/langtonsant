import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1856 : checkSingleBlackFast (-58, -40) 28459 .east (32, 20) (-9, -42) = true := by
  decide +kernel

end LangtonsAnt
