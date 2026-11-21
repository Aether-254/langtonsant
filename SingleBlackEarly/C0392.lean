import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0392 : checkSingleBlackFast (11, -3) 5090 .south (-3, -11) (-10, -14) = true := by
  decide +kernel

end LangtonsAnt
