import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1801 : checkSingleBlackFast2 (-56, -31) 17707 .east (16, 19) (-6, -36) = true := by
  decide +kernel

end LangtonsAnt
