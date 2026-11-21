import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0177 : checkSingleBlackFast (-8, 6) 9708 .north (-5, -5) (-27, -9) = true := by
  decide +kernel

end LangtonsAnt
