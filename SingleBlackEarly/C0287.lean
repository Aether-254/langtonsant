import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0287 : checkSingleBlackFast (15, 12) 5732 .south (-11, -8) (-17, -12) = true := by
  decide +kernel

end LangtonsAnt
