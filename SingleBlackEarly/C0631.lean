import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0631 : checkSingleBlackFast (8, -9) 14888 .north (-2, -5) (-26, -3) = true := by
  decide +kernel

end LangtonsAnt
