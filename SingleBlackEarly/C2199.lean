import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2199 : checkSingleBlackFast2 (-92, -69) 16031 .west (33, 43) (-62, 23) = true := by
  decide +kernel

end LangtonsAnt
