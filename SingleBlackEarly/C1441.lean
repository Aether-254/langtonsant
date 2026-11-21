import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1441 : checkSingleBlackFast2 (-19, -1) 17612 .north (-1, -6) (-33, -12) = true := by
  decide +kernel

end LangtonsAnt
