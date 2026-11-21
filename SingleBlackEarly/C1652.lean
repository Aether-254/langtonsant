import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1652 : checkSingleBlackFast2 (-43, -20) 18709 .east (19, 4) (-4, -38) = true := by
  decide +kernel

end LangtonsAnt
