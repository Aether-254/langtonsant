import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0673 : checkSingleBlackFast (16, -11) 9598 .south (-11, 4) (-22, -11) = true := by
  decide +kernel

end LangtonsAnt
