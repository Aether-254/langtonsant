import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1705 : checkSingleBlackFast (-43, -25) 11696 .north (11, 3) (-37, -19) = true := by
  decide +kernel

end LangtonsAnt
