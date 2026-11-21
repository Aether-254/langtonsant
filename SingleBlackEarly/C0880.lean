import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0880 : checkSingleBlackFast (-9, -1) 10080 .north (-2, 0) (-24, 4) = true := by
  decide +kernel

end LangtonsAnt
