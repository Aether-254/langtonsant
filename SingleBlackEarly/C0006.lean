import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0006 : checkSingleBlackFast (0, 1) 1547 .west (-5, 2) (-11, -5) = true := by
  decide +kernel

end LangtonsAnt
