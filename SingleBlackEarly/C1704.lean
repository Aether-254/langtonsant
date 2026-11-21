import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1704 : checkSingleBlackFast2 (-44, -24) 15196 .north (17, 7) (-43, -23) = true := by
  decide +kernel

end LangtonsAnt
