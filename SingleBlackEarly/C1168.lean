import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1168 : checkSingleBlack (27, -19) 10436 .north (-2, 0) (-26, 2) = true := by
  decide +kernel

end LangtonsAnt
