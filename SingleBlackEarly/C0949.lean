import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0949 : checkSingleBlackFast2 (13, 17) 18056 .north (-7, 8) (-7, -26) = true := by
  decide +kernel

end LangtonsAnt
