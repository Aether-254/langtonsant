import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1878 : checkSingleBlackFast (-60, -42) 28563 .east (33, 21) (-8, -43) = true := by
  decide +kernel

end LangtonsAnt
