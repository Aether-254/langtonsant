import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0898 : checkSingleBlack (-8, 11) 18991 .east (-11, -6) (-31, -3) = true := by
  decide +kernel

end LangtonsAnt
