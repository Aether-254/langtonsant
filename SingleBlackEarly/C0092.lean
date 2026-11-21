import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0092 : checkSingleBlackFast (3, 5) 1860 .south (-4, -1) (-12, -5) = true := by
  decide +kernel

end LangtonsAnt
