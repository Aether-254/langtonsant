import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1506 : checkSingleBlackFast (-26, -6) 27280 .north (-2, 8) (-12, -36) = true := by
  decide +kernel

end LangtonsAnt
