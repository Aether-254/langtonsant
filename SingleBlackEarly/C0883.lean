import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0883 : checkSingleBlackFast (-11, -2) 11124 .north (1, 0) (-25, -16) = true := by
  decide +kernel

end LangtonsAnt
