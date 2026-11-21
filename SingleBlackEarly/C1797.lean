import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1797 : checkSingleBlackFast (-56, -30) 12420 .north (17, 9) (-43, -25) = true := by
  decide +kernel

end LangtonsAnt
