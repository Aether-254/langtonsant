import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0776 : checkSingleBlackFast2 (23, -15) 10920 .north (-3, 4) (-27, 6) = true := by
  decide +kernel

end LangtonsAnt
