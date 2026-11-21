import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0175 : checkSingleBlackFast (-7, 5) 11052 .north (-4, 7) (2, -21) = true := by
  decide +kernel

end LangtonsAnt
