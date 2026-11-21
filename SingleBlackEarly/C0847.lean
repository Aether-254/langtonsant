import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0847 : checkSingleBlackFast (-7, 8) 12994 .north (0, -2) (-29, 5) = true := by
  decide +kernel

end LangtonsAnt
