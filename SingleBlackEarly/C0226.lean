import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0226 : checkSingleBlackFast (8, 8) 6407 .east (-2, -8) (-17, -14) = true := by
  decide +kernel

end LangtonsAnt
