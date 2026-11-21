import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0418 : checkSingleBlackFast2 (17, -1) 17620 .north (-8, -5) (-26, -19) = true := by
  decide +kernel

end LangtonsAnt
