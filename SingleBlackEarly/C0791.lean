import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0791 : checkSingleBlackFast (25, -8) 11876 .north (-9, -2) (-33, 0) = true := by
  decide +kernel

end LangtonsAnt
