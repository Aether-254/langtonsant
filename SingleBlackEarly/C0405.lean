import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0405 : checkSingleBlackFast (15, -6) 7684 .north (-2, 1) (-18, -11) = true := by
  decide +kernel

end LangtonsAnt
