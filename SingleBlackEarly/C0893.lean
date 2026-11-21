import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0893 : checkSingleBlackFast2 (-7, -3) 15396 .south (-3, -12) (-17, -28) = true := by
  decide +kernel

end LangtonsAnt
