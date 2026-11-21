import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2119 : checkSingleBlackFast (-82, -63) 22064 .north (43, 39) (-69, -31) = true := by
  decide +kernel

end LangtonsAnt
