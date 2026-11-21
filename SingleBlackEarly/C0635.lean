import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0635 : checkSingleBlackFast2 (11, -7) 15351 .west (-7, 5) (-26, -5) = true := by
  decide +kernel

end LangtonsAnt
