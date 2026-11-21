import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1072 : checkSingleBlackFast2 (-16, -4) 10580 .north (0, 0) (-26, 0) = true := by
  decide +kernel

end LangtonsAnt
