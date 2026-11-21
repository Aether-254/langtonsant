import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1640 : checkSingleBlackFast2 (-41, -15) 11476 .north (9, 1) (-35, -17) = true := by
  decide +kernel

end LangtonsAnt
