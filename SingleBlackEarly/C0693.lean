import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0693 : checkSingleBlackFast (21, -10) 10032 .north (-1, -4) (-25, -2) = true := by
  decide +kernel

end LangtonsAnt
