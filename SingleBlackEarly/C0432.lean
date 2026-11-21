import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0432 : checkSingleBlackFast (19, 3) 9396 .north (-3, 4) (-23, -14) = true := by
  decide +kernel

end LangtonsAnt
