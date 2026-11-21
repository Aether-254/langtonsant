import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0134 : checkSingleBlackFast (5, -2) 1540 .south (-6, -5) (-10, -7) = true := by
  decide +kernel

end LangtonsAnt
