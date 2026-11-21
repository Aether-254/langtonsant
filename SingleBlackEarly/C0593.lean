import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0593 : checkSingleBlackFast (20, 14) 9028 .north (-9, 5) (-1, -21) = true := by
  decide +kernel

end LangtonsAnt
