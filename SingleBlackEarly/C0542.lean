import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0542 : checkSingleBlackFast2 (8, -5) 17600 .south (-2, -5) (-26, -19) = true := by
  decide +kernel

end LangtonsAnt
