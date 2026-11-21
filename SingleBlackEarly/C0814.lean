import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0814 : checkSingleBlackFast (26, -4) 21884 .south (-18, 0) (-20, -28) = true := by
  decide +kernel

end LangtonsAnt
