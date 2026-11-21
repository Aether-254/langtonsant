import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0160 : checkSingleBlackFast (-1, 9) 3784 .north (0, -2) (-16, -4) = true := by
  decide +kernel

end LangtonsAnt
