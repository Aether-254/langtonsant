import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0238 : checkSingleBlackFast (2, 10) 1982 .north (2, -2) (-11, -3) = true := by
  decide +kernel

end LangtonsAnt
