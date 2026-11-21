import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1772 : checkSingleBlackFast2 (-53, -27) 12100 .north (15, 7) (-41, -23) = true := by
  decide +kernel

end LangtonsAnt
