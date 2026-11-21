import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0213 : checkSingleBlackFast (8, 7) 2789 .east (-2, -8) (-14, -1) = true := by
  decide +kernel

end LangtonsAnt
