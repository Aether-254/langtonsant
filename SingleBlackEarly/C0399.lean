import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0399 : checkSingleBlackFast (13, -6) 5689 .west (-8, 3) (-17, -15) = true := by
  decide +kernel

end LangtonsAnt
