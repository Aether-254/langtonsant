import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0064 : checkSingleBlackFast (-5, -3) 5779 .west (2, 3) (-18, -8) = true := by
  decide +kernel

end LangtonsAnt
