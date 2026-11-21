import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1881 : checkSingleBlackFast (-59, -41) 12528 .north (19, 11) (-45, -27) = true := by
  decide +kernel

end LangtonsAnt
