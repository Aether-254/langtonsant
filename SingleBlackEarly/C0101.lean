import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0101 : checkSingleBlackFast (-4, 5) 2434 .north (2, -2) (-15, -5) = true := by
  decide +kernel

end LangtonsAnt
