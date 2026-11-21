import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0959 : checkSingleBlackFast (7, 18) 8612 .north (-1, -3) (-23, 1) = true := by
  decide +kernel

end LangtonsAnt
