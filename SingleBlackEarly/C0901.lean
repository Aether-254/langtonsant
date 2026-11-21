import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0901 : checkSingleBlackFast (-9, 12) 25736 .north (-2, 9) (-6, -29) = true := by
  decide +kernel

end LangtonsAnt
