import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1390 : checkSingleBlackFast (-17, 4) 25528 .north (4, 10) (-4, -32) = true := by
  decide +kernel

end LangtonsAnt
