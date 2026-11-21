import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0234 : checkSingleBlackFast2 (3, 8) 17445 .west (-2, 2) (-28, -9) = true := by
  decide +kernel

end LangtonsAnt
