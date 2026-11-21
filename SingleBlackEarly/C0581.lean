import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0581 : checkSingleBlackFast (19, 0) 8394 .north (-8, 6) (-7, -17) = true := by
  decide +kernel

end LangtonsAnt
