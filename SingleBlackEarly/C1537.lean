import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1537 : checkSingleBlackFast (-32, -7) 27476 .north (7, 15) (-7, -33) = true := by
  decide +kernel

end LangtonsAnt
