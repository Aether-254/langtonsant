import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0695 : checkSingleBlackFast (21, -9) 13760 .north (-5, -1) (-29, 1) = true := by
  decide +kernel

end LangtonsAnt
