import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1485 : checkSingleBlackFast (-23, -5) 10656 .north (1, 0) (-27, -2) = true := by
  decide +kernel

end LangtonsAnt
