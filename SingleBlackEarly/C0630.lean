import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0630 : checkSingleBlackFast (9, -9) 9240 .south (-8, -1) (-20, -17) = true := by
  decide +kernel

end LangtonsAnt
