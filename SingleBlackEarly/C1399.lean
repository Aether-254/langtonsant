import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1399 : checkSingleBlackFast (-20, 7) 10548 .north (0, 0) (-26, 0) = true := by
  decide +kernel

end LangtonsAnt
