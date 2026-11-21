import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0782 : checkSingleBlackFast2 (23, -14) 10608 .north (-4, -2) (-28, 0) = true := by
  decide +kernel

end LangtonsAnt
