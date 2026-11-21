import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2189 : checkSingleBlackFast (-87, -69) 13984 .north (33, 25) (-59, -41) = true := by
  decide +kernel

end LangtonsAnt
