import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0974 : checkSingleBlackFast2 (1, 18) 10532 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
