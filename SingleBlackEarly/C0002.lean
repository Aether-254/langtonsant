import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0002 : checkSingleBlackFast (1, -1) 19710 .north (15, -1) (-24, -14) = true := by
  decide +kernel

end LangtonsAnt
