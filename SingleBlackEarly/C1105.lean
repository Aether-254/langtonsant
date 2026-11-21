import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1105 : checkSingleBlackFast (-1, -9) 11568 .north (3, 1) (-29, -5) = true := by
  decide +kernel

end LangtonsAnt
