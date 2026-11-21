import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1580 : checkSingleBlackFast (-35, -10) 19607 .east (20, -4) (-23, -38) = true := by
  decide +kernel

end LangtonsAnt
