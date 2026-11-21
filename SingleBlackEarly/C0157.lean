import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0157 : checkSingleBlackFast (0, 8) 8566 .south (-10, -3) (-23, -4) = true := by
  decide +kernel

end LangtonsAnt
