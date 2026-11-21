import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0728 : checkSingleBlackFast2 (8, -12) 10856 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
