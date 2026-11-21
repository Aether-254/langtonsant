import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1597 : checkSingleBlackFast (-38, -11) 11368 .north (7, 0) (-33, -14) = true := by
  decide +kernel

end LangtonsAnt
