import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0540 : checkSingleBlackFast (7, -5) 35428 .south (-6, -17) (-34, -1) = true := by
  decide +kernel

end LangtonsAnt
