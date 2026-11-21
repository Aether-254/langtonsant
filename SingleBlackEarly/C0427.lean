import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0427 : checkSingleBlackFast (17, 2) 7037 .west (-17, 3) (-15, -18) = true := by
  decide +kernel

end LangtonsAnt
