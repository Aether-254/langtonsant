import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0867 : checkSingleBlackFast (-7, 2) 6542 .north (-2, 1) (-21, -6) = true := by
  decide +kernel

end LangtonsAnt
