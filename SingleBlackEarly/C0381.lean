import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0381 : checkSingleBlackFast (14, -1) 11198 .north (-1, 2) (-10, -23) = true := by
  decide +kernel

end LangtonsAnt
