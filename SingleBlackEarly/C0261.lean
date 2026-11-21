import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0261 : checkSingleBlackFast (10, 11) 2392 .south (-11, -9) (-17, -9) = true := by
  decide +kernel

end LangtonsAnt
