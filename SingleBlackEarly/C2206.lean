import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2206 : checkSingleBlackFast (-92, -71) 21277 .east (37, 27) (21, -60) = true := by
  decide +kernel

end LangtonsAnt
