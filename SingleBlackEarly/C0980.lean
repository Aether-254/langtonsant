import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0980 : checkSingleBlackFast (-1, 18) 8308 .north (-1, -2) (-23, 2) = true := by
  decide +kernel

end LangtonsAnt
