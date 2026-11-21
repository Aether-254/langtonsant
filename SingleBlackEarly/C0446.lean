import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0446 : checkSingleBlackFast (18, 6) 8766 .south (-8, -4) (-23, -5) = true := by
  decide +kernel

end LangtonsAnt
