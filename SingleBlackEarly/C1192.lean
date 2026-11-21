import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1192 : checkSingleBlackFast2 (25, 3) 10512 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
