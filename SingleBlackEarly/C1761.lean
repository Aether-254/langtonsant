import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1761 : checkSingleBlackFast2 (-52, -30) 18507 .east (16, 10) (-17, -28) = true := by
  decide +kernel

end LangtonsAnt
