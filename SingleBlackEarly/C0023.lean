import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0023 : checkSingleBlackFast (2, 1) 1232 .south (-4, -6) (-10, -4) = true := by
  decide +kernel

end LangtonsAnt
