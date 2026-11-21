import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0657 : checkSingleBlackFast2 (12, -11) 15736 .north (-6, 2) (-28, 6) = true := by
  decide +kernel

end LangtonsAnt
