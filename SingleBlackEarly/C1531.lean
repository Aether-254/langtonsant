import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1531 : checkSingleBlackFast (-32, -5) 11056 .north (4, 0) (-30, -8) = true := by
  decide +kernel

end LangtonsAnt
