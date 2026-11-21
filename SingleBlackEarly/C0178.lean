import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0178 : checkSingleBlackFast (-6, 5) 4900 .north (-2, -3) (-20, -7) = true := by
  decide +kernel

end LangtonsAnt
