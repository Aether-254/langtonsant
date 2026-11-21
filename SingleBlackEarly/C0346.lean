import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0346 : checkSingleBlackFast2 (-4, 12) 15618 .south (-11, 0) (-28, 1) = true := by
  decide +kernel

end LangtonsAnt
