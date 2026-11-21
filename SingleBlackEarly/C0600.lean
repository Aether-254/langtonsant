import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0600 : checkSingleBlackFast (18, 16) 9652 .north (-6, 6) (0, -22) = true := by
  decide +kernel

end LangtonsAnt
