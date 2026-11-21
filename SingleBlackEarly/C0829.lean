import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0829 : checkSingleBlackFast (22, 2) 7398 .south (-20, -1) (-25, -12) = true := by
  decide +kernel

end LangtonsAnt
