import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0026 : checkSingleBlackFast (3, 2) 741 .east (0, -5) (-7, -3) = true := by
  decide +kernel

end LangtonsAnt
