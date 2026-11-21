import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0836 : checkSingleBlackFast (4, 16) 8626 .north (1, -2) (-24, -13) = true := by
  decide +kernel

end LangtonsAnt
