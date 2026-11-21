import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0173 : checkSingleBlackFast (-7, 6) 8572 .north (2, -1) (-26, 1) = true := by
  decide +kernel

end LangtonsAnt
