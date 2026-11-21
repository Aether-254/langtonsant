import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1784 : checkSingleBlackFast (-55, -32) 19333 .east (25, 10) (2, -44) = true := by
  decide +kernel

end LangtonsAnt
