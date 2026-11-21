import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0477 : checkSingleBlackFast (5, 10) 10115 .east (-1, -9) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
