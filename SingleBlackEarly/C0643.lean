import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0643 : checkSingleBlackFast (6, -10) 11092 .south (-11, -4) (-19, -16) = true := by
  decide +kernel

end LangtonsAnt
