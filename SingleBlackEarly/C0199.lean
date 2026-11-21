import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0199 : checkSingleBlackFast (9, 3) 5218 .north (6, -5) (-17, -8) = true := by
  decide +kernel

end LangtonsAnt
