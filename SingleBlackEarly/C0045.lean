import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0045 : checkSingleBlackFast (-4, 2) 2132 .south (-3, -3) (-13, -9) = true := by
  decide +kernel

end LangtonsAnt
