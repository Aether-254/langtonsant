import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0536 : checkSingleBlack (-1, -7) 14783 .west (-5, 8) (-31, -7) = true := by
  decide +kernel

end LangtonsAnt
