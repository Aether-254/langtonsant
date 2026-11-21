import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0379 : checkSingleBlackFast (16, -1) 11426 .north (-1, 3) (-10, -22) = true := by
  decide +kernel

end LangtonsAnt
