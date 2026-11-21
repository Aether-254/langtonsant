import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0680 : checkSingleBlackFast (18, -9) 10240 .north (1, -2) (-23, 0) = true := by
  decide +kernel

end LangtonsAnt
