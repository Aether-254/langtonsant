import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1419 : checkSingleBlackFast (-17, 1) 32484 .south (-11, -17) (-39, -7) = true := by
  decide +kernel

end LangtonsAnt
