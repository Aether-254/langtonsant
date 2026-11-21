import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0100 : checkSingleBlackFast (-2, 5) 1580 .north (5, 4) (-9, -6) = true := by
  decide +kernel

end LangtonsAnt
