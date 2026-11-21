import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0925 : checkSingleBlackFast (-12, 13) 14740 .north (-2, 8) (-2, -26) = true := by
  decide +kernel

end LangtonsAnt
