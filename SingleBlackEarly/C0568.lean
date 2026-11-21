import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0568 : checkSingleBlackFast (20, -4) 8292 .south (-12, -6) (-20, -16) = true := by
  decide +kernel

end LangtonsAnt
