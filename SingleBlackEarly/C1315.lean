import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1315 : checkSingleBlackFast (-11, 17) 14216 .north (-1, 5) (1, -27) = true := by
  decide +kernel

end LangtonsAnt
