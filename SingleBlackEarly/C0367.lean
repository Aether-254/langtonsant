import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0367 : checkSingleBlackFast (13, 2) 5092 .south (-10, -6) (-18, -12) = true := by
  decide +kernel

end LangtonsAnt
