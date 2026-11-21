import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0663 : checkSingleBlackFast (13, -9) 6112 .north (-3, 0) (-17, -10) = true := by
  decide +kernel

end LangtonsAnt
