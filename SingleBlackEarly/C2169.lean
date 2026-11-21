import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2169 : checkSingleBlackFast (-90, -63) 14072 .north (33, 25) (-59, -41) = true := by
  decide +kernel

end LangtonsAnt
