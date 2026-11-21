import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0854 : checkSingleBlackFast (-9, 8) 7347 .east (1, -3) (-18, -21) = true := by
  decide +kernel

end LangtonsAnt
