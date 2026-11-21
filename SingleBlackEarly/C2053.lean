import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2053 : checkSingleBlackFast (-76, -57) 21752 .north (40, 36) (-66, -28) = true := by
  decide +kernel

end LangtonsAnt
