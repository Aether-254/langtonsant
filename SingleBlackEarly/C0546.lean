import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0546 : checkSingleBlackFast2 (9, -4) 18390 .north (-6, -4) (-25, -21) = true := by
  decide +kernel

end LangtonsAnt
