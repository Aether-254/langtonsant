import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1024 : checkSingleBlackFast2 (-6, 18) 15280 .north (-10, 5) (-6, -25) = true := by
  decide +kernel

end LangtonsAnt
