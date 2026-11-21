import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2110 : checkSingleBlackFast2 (-83, -61) 17041 .west (29, 38) (-58, 18) = true := by
  decide +kernel

end LangtonsAnt
