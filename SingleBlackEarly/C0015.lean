import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0015 : checkSingleBlackFast (-2, -3) 12456 .south (-4, 5) (-18, -19) = true := by
  decide +kernel

end LangtonsAnt
