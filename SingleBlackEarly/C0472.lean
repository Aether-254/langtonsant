import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0472 : checkSingleBlackFast (11, 14) 9228 .north (-6, 9) (0, -19) = true := by
  decide +kernel

end LangtonsAnt
