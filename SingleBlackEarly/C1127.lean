import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1127 : checkSingleBlackFast (25, -17) 10776 .north (-2, 2) (-26, 4) = true := by
  decide +kernel

end LangtonsAnt
