import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0082 : checkSingleBlackFast (6, -3) 6990 .north (4, -2) (-19, -7) = true := by
  decide +kernel

end LangtonsAnt
