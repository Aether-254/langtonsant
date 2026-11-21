import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0141 : checkSingleBlackFast (6, 1) 1604 .south (-4, -5) (-10, -5) = true := by
  decide +kernel

end LangtonsAnt
