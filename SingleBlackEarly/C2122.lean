import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2122 : checkSingleBlackFast2 (-82, -62) 17172 .north (36, 26) (-62, -42) = true := by
  decide +kernel

end LangtonsAnt
