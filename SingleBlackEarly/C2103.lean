import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2103 : checkSingleBlackFast (-84, -57) 13760 .north (30, 22) (-56, -38) = true := by
  decide +kernel

end LangtonsAnt
