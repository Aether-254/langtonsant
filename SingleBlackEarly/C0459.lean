import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0459 : checkSingleBlackFast (18, 12) 9900 .north (-6, 7) (0, -21) = true := by
  decide +kernel

end LangtonsAnt
