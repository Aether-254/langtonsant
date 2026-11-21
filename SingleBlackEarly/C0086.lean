import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0086 : checkSingleBlackFast (4, 3) 3148 .south (-1, -5) (-13, -5) = true := by
  decide +kernel

end LangtonsAnt
