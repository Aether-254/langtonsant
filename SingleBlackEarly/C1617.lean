import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1617 : checkSingleBlackFast (-35, -17) 11280 .north (7, 0) (-33, -14) = true := by
  decide +kernel

end LangtonsAnt
