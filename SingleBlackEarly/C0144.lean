import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0144 : checkSingleBlackFast (7, 3) 2128 .north (2, 3) (-12, -7) = true := by
  decide +kernel

end LangtonsAnt
