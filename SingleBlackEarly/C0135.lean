import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0135 : checkSingleBlackFast (6, 0) 3389 .west (-9, -2) (-8, -10) = true := by
  decide +kernel

end LangtonsAnt
