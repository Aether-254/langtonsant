import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1079 : checkSingleBlackFast (-13, -5) 10420 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
