import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1188 : checkSingleBlackFast2 (24, 0) 10452 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
