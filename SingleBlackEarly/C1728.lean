import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1728 : checkSingleBlackFast2 (-49, -23) 11892 .north (13, 5) (-39, -21) = true := by
  decide +kernel

end LangtonsAnt
