import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0805 : checkSingleBlackFast (22, -6) 6092 .south (-15, 0) (-21, -2) = true := by
  decide +kernel

end LangtonsAnt
