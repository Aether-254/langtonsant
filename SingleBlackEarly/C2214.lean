import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2214 : checkSingleBlackFast2 (-94, -66) 18865 .west (40, 46) (-66, 23) = true := by
  decide +kernel

end LangtonsAnt
