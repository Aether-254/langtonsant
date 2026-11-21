import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0365 : checkSingleBlackFast (12, 1) 5104 .south (-10, -6) (-18, -12) = true := by
  decide +kernel

end LangtonsAnt
