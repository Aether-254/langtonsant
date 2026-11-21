import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1296 : checkSingleBlackFast2 (-6, 21) 10452 .north (-1, -1) (-25, 1) = true := by
  decide +kernel

end LangtonsAnt
