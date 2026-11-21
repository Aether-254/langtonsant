import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1948 : checkSingleBlackFast2 (-69, -43) 12932 .north (23, 15) (-49, -31) = true := by
  decide +kernel

end LangtonsAnt
