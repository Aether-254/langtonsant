import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2142 : checkSingleBlackFast (-84, -66) 29811 .east (45, 33) (4, -55) = true := by
  decide +kernel

end LangtonsAnt
