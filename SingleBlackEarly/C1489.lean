import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1489 : checkSingleBlackFast (-28, -2) 10964 .north (3, 0) (-29, -6) = true := by
  decide +kernel

end LangtonsAnt
