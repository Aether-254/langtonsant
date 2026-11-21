import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1596 : checkSingleBlackFast2 (-37, -11) 11268 .north (7, 0) (-33, -14) = true := by
  decide +kernel

end LangtonsAnt
