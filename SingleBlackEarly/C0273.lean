import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0273 : checkSingleBlackFast (14, 8) 2703 .east (-4, -4) (-9, -12) = true := by
  decide +kernel

end LangtonsAnt
