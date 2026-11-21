import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0895 : checkSingleBlackFast (-6, 10) 12164 .north (-6, 6) (0, -22) = true := by
  decide +kernel

end LangtonsAnt
