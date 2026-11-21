import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0094 : checkSingleBlackFast (2, 5) 3068 .north (6, -2) (-16, -10) = true := by
  decide +kernel

end LangtonsAnt
