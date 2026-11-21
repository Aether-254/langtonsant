import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0091 : checkSingleBlackFast (3, 4) 3688 .north (5, 4) (-15, -8) = true := by
  decide +kernel

end LangtonsAnt
