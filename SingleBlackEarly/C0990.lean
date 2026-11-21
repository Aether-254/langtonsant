import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0990 : checkSingleBlackFast (-4, 17) 8228 .north (-1, -1) (-23, 3) = true := by
  decide +kernel

end LangtonsAnt
