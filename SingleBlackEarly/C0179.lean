import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0179 : checkSingleBlackFast (-5, 2) 12394 .south (1, -6) (-26, -17) = true := by
  decide +kernel

end LangtonsAnt
