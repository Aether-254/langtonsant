import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0057 : checkSingleBlackFast (2, -1) 5196 .north (0, 12) (-16, -16) = true := by
  decide +kernel

end LangtonsAnt
