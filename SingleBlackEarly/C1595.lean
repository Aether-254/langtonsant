import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1595 : checkSingleBlackFast (-33, -15) 11176 .north (6, 0) (-32, -12) = true := by
  decide +kernel

end LangtonsAnt
