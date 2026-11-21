import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1032 : checkSingleBlackFast (-7, 16) 8051 .east (-2, -3) (-18, -18) = true := by
  decide +kernel

end LangtonsAnt
