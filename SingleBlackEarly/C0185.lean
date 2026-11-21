import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0185 : checkSingleBlackFast (8, -3) 2363 .east (-1, -4) (-9, -9) = true := by
  decide +kernel

end LangtonsAnt
