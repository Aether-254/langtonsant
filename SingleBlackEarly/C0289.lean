import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0289 : checkSingleBlackFast (13, 13) 6448 .south (-11, -10) (-19, -10) = true := by
  decide +kernel

end LangtonsAnt
