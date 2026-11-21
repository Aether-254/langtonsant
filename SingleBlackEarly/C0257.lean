import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0257 : checkSingleBlackFast (13, 9) 5399 .west (-8, -3) (-22, -2) = true := by
  decide +kernel

end LangtonsAnt
