import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2159 : checkSingleBlackFast2 (-89, -65) 15927 .west (31, 42) (-61, 23) = true := by
  decide +kernel

end LangtonsAnt
