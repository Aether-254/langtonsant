import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0560 : checkSingleBlackFast2 (19, -5) 12715 .west (-2, -3) (-24, -10) = true := by
  decide +kernel

end LangtonsAnt
