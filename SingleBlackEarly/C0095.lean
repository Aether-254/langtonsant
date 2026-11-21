import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0095 : checkSingleBlackFast (2, 6) 2552 .north (0, -1) (-12, -9) = true := by
  decide +kernel

end LangtonsAnt
