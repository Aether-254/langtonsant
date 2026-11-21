import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0858 : checkSingleBlackFast2 (-10, 8) 15479 .west (-6, 4) (-27, -10) = true := by
  decide +kernel

end LangtonsAnt
