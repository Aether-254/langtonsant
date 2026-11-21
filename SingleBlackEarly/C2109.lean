import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2109 : checkSingleBlackFast (-84, -59) 19163 .east (30, 33) (8, -50) = true := by
  decide +kernel

end LangtonsAnt
