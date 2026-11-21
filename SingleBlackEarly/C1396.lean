import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1396 : checkSingleBlackFast2 (-16, 4) 25521 .east (-5, -13) (-33, -16) = true := by
  decide +kernel

end LangtonsAnt
