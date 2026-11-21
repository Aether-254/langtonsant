import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1522 : checkSingleBlackFast (-29, -8) 22472 .north (0, 7) (-6, -33) = true := by
  decide +kernel

end LangtonsAnt
