import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0584 : checkSingleBlackFast (20, 5) 39810 .north (-3, 8) (-36, -19) = true := by
  decide +kernel

end LangtonsAnt
