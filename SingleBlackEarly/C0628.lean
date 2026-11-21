import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0628 : checkSingleBlackFast (8, -8) 9152 .north (2, -5) (-22, -3) = true := by
  decide +kernel

end LangtonsAnt
