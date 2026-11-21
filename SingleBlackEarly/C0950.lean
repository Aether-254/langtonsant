import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0950 : checkSingleBlackFast (14, 17) 8724 .north (-1, -3) (-23, 1) = true := by
  decide +kernel

end LangtonsAnt
