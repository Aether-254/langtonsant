import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0796 : checkSingleBlackFast2 (24, -6) 16216 .north (-16, 14) (-12, -22) = true := by
  decide +kernel

end LangtonsAnt
