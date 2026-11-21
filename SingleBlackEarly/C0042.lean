import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0042 : checkSingleBlackFast (-3, 3) 1374 .south (-3, -4) (-10, -7) = true := by
  decide +kernel

end LangtonsAnt
