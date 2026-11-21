import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1817 : checkSingleBlackFast (-58, -31) 12408 .north (17, 9) (-43, -25) = true := by
  decide +kernel

end LangtonsAnt
