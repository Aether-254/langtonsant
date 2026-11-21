import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0664 : checkSingleBlackFast2 (14, -9) 15711 .east (-9, -4) (-31, -9) = true := by
  decide +kernel

end LangtonsAnt
