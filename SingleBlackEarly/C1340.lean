import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1340 : checkSingleBlackFast (-16, 14) 23620 .north (13, 1) (-39, -25) = true := by
  decide +kernel

end LangtonsAnt
