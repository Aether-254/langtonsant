import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1413 : checkSingleBlackFast2 (-19, 1) 23448 .north (-5, 2) (-5, -32) = true := by
  decide +kernel

end LangtonsAnt
