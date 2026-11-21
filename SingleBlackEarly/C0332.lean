import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0332 : checkSingleBlackFast (3, 12) 6519 .west (-5, 0) (-17, -3) = true := by
  decide +kernel

end LangtonsAnt
