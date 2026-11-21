import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1802 : checkSingleBlackFast2 (-55, -33) 15585 .west (15, 24) (-44, 4) = true := by
  decide +kernel

end LangtonsAnt
