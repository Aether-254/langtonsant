import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0470 : checkSingleBlackFast2 (12, 14) 15452 .south (-9, -13) (-29, -23) = true := by
  decide +kernel

end LangtonsAnt
