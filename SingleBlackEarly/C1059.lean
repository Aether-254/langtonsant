import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1059 : checkSingleBlackFast (-14, 0) 9534 .north (-3, 1) (-20, -14) = true := by
  decide +kernel

end LangtonsAnt
