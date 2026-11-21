import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0806 : checkSingleBlackFast (21, -6) 10208 .north (-1, -2) (-25, 0) = true := by
  decide +kernel

end LangtonsAnt
