import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1065 : checkSingleBlackFast (-16, -3) 32801 .east (5, -14) (-10, -42) = true := by
  decide +kernel

end LangtonsAnt
