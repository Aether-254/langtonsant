import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0187 : checkSingleBlackFast (10, -1) 8506 .south (-6, -2) (-23, -11) = true := by
  decide +kernel

end LangtonsAnt
