import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1827 : checkSingleBlackFast2 (-58, -36) 18819 .east (19, 13) (-14, -31) = true := by
  decide +kernel

end LangtonsAnt
