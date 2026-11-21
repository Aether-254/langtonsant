import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0118 : checkSingleBlackFast (6, 6) 5600 .south (-7, 2) (-15, -12) = true := by
  decide +kernel

end LangtonsAnt
