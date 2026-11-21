import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0368 : checkSingleBlackFast (12, 3) 9678 .south (-11, 7) (-22, -12) = true := by
  decide +kernel

end LangtonsAnt
