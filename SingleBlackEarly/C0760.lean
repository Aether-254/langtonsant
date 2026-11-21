import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0760 : checkSingleBlackFast2 (18, -15) 12912 .north (-9, 2) (-33, 4) = true := by
  decide +kernel

end LangtonsAnt
