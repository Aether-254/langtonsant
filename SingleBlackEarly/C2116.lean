import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2116 : checkSingleBlackFast2 (-83, -62) 16002 .north (35, 23) (-62, -34) = true := by
  decide +kernel

end LangtonsAnt
