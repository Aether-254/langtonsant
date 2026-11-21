import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0997 : checkSingleBlackFast2 (-9, 14) 16371 .west (2, 8) (-27, -16) = true := by
  decide +kernel

end LangtonsAnt
