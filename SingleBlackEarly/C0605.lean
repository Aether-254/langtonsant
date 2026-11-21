import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0605 : checkSingleBlackFast (15, 15) 9360 .north (-6, 8) (0, -20) = true := by
  decide +kernel

end LangtonsAnt
