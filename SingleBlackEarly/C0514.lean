import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0514 : checkSingleBlackFast (-6, -4) 5861 .west (-14, -4) (-14, -17) = true := by
  decide +kernel

end LangtonsAnt
