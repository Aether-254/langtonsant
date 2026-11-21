import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0020 : checkSingleBlackFast (1, -2) 848 .north (4, 5) (-8, -3) = true := by
  decide +kernel

end LangtonsAnt
