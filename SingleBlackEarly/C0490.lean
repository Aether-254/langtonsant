import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0490 : checkSingleBlackFast (4, 14) 29079 .east (6, -3) (-26, -28) = true := by
  decide +kernel

end LangtonsAnt
