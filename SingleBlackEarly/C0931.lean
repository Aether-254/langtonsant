import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0931 : checkSingleBlackFast2 (-13, 11) 15592 .north (-3, 6) (-3, -28) = true := by
  decide +kernel

end LangtonsAnt
