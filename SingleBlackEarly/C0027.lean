import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0027 : checkSingleBlackFast (3, 1) 942 .south (-7, -6) (-8, -3) = true := by
  decide +kernel

end LangtonsAnt
