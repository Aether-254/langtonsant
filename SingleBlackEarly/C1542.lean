import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1542 : checkSingleBlackFast (-33, -10) 32989 .east (10, -11) (-31, -17) = true := by
  decide +kernel

end LangtonsAnt
