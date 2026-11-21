import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0025 : checkSingleBlackFast (2, 2) 1747 .west (1, 4) (-13, -3) = true := by
  decide +kernel

end LangtonsAnt
