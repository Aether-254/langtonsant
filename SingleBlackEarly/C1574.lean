import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1574 : checkSingleBlackFast2 (-35, -9) 11164 .north (6, 0) (-32, -12) = true := by
  decide +kernel

end LangtonsAnt
