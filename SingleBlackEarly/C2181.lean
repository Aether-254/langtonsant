import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2181 : checkSingleBlackFast2 (-91, -67) 16031 .west (32, 43) (-62, 24) = true := by
  decide +kernel

end LangtonsAnt
