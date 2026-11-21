import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0822 : checkSingleBlackFast2 (22, -3) 11057 .west (-12, 6) (-22, -19) = true := by
  decide +kernel

end LangtonsAnt
