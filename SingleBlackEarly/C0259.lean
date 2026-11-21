import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0259 : checkSingleBlackFast (11, 11) 13680 .north (-1, -14) (-29, -10) = true := by
  decide +kernel

end LangtonsAnt
