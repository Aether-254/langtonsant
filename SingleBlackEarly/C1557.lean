import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1557 : checkSingleBlackFast (-35, -7) 26762 .south (7, -8) (-38, -19) = true := by
  decide +kernel

end LangtonsAnt
