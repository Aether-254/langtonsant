import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1656 : checkSingleBlackFast (-42, -21) 28237 .east (11, -7) (1, -40) = true := by
  decide +kernel

end LangtonsAnt
