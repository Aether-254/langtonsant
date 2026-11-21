import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0164 : checkSingleBlackFast (-2, 8) 10322 .north (-3, 1) (-24, -18) = true := by
  decide +kernel

end LangtonsAnt
