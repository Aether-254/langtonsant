import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2093 : checkSingleBlackFast2 (-83, -59) 15615 .west (28, 39) (-58, 20) = true := by
  decide +kernel

end LangtonsAnt
