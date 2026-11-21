import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0710 : checkSingleBlackFast2 (2, -11) 15564 .north (-4, 11) (-8, -27) = true := by
  decide +kernel

end LangtonsAnt
