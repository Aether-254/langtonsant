import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1409 : checkSingleBlackFast (-20, 2) 11427 .east (-2, -7) (-26, -18) = true := by
  decide +kernel

end LangtonsAnt
