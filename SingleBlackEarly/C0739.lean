import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0739 : checkSingleBlackFast (18, -13) 10896 .north (-2, 1) (-26, 3) = true := by
  decide +kernel

end LangtonsAnt
