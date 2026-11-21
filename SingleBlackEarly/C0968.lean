import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0968 : checkSingleBlackFast (4, 19) 28476 .north (0, 0) (-2, -36) = true := by
  decide +kernel

end LangtonsAnt
