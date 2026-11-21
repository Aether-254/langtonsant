import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0889 : checkSingleBlackFast (-8, -4) 13396 .south (-13, 1) (-27, -7) = true := by
  decide +kernel

end LangtonsAnt
