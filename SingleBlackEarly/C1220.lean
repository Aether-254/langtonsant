import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1220 : checkSingleBlackFast2 (21, 9) 10600 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
