import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1465 : checkSingleBlackFast (-26, 1) 10732 .north (1, 0) (-27, -2) = true := by
  decide +kernel

end LangtonsAnt
