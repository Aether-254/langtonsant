import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0911 : checkSingleBlackFast (-10, 6) 8040 .north (-1, -2) (-23, -4) = true := by
  decide +kernel

end LangtonsAnt
