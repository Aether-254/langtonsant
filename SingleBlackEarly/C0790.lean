import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0790 : checkSingleBlackFast2 (24, -8) 15060 .north (-6, 4) (-30, 6) = true := by
  decide +kernel

end LangtonsAnt
