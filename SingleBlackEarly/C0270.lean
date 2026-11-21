import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0270 : checkSingleBlackFast2 (14, 5) 11053 .west (-3, 1) (-19, -10) = true := by
  decide +kernel

end LangtonsAnt
