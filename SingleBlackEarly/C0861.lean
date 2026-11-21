import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0861 : checkSingleBlackFast (-7, 3) 9384 .north (0, -4) (-24, -6) = true := by
  decide +kernel

end LangtonsAnt
