import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0865 : checkSingleBlackFast2 (-9, 2) 16956 .south (-11, -14) (-25, -24) = true := by
  decide +kernel

end LangtonsAnt
