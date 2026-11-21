import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2198 : checkSingleBlackFast2 (-91, -69) 17457 .west (33, 42) (-62, 22) = true := by
  decide +kernel

end LangtonsAnt
