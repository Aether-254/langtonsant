import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0920 : checkSingleBlackFast (-7, 11) 9544 .north (0, 1) (-26, 1) = true := by
  decide +kernel

end LangtonsAnt
