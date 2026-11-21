import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0445 : checkSingleBlackFast (18, 7) 9750 .north (4, -4) (-23, -17) = true := by
  decide +kernel

end LangtonsAnt
