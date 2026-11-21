import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0058 : checkSingleBlackFast (3, 0) 4844 .south (-3, -1) (-15, -15) = true := by
  decide +kernel

end LangtonsAnt
