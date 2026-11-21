import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0588 : checkSingleBlackFast2 (21, 5) 10732 .north (-5, 7) (-1, -23) = true := by
  decide +kernel

end LangtonsAnt
