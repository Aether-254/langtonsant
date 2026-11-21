import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1443 : checkSingleBlackFast (-24, 3) 21476 .north (-2, -7) (-32, -11) = true := by
  decide +kernel

end LangtonsAnt
