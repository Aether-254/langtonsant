import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0397 : checkSingleBlackFast (12, -6) 5134 .south (-8, -5) (-17, -12) = true := by
  decide +kernel

end LangtonsAnt
