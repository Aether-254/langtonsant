import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1726 : checkSingleBlackFast2 (-46, -26) 15300 .north (18, 8) (-44, -24) = true := by
  decide +kernel

end LangtonsAnt
