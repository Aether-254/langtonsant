import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1861 : checkSingleBlackFast (-62, -35) 12616 .north (19, 11) (-45, -27) = true := by
  decide +kernel

end LangtonsAnt
