import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0539 : checkSingleBlackFast (7, -4) 6328 .north (-1, -1) (-15, -11) = true := by
  decide +kernel

end LangtonsAnt
