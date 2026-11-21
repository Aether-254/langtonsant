import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0579 : checkSingleBlackFast (21, 0) 13300 .north (-3, 1) (-27, 3) = true := by
  decide +kernel

end LangtonsAnt
