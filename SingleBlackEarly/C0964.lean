import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0964 : checkSingleBlackFast (4, 17) 8572 .north (-1, -3) (-23, 1) = true := by
  decide +kernel

end LangtonsAnt
