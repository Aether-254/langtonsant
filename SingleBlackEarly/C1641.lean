import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1641 : checkSingleBlackFast (-42, -15) 11576 .north (9, 1) (-35, -17) = true := by
  decide +kernel

end LangtonsAnt
