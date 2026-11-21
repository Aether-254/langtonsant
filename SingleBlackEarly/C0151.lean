import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0151 : checkSingleBlackFast (0, 6) 1620 .south (-4, -4) (-10, -6) = true := by
  decide +kernel

end LangtonsAnt
