import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0800 : checkSingleBlackFast2 (23, -5) 11228 .north (-2, 1) (-26, 3) = true := by
  decide +kernel

end LangtonsAnt
