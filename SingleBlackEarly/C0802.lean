import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0802 : checkSingleBlackFast (22, -5) 10256 .north (-1, -2) (-25, 0) = true := by
  decide +kernel

end LangtonsAnt
