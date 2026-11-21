import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0578 : checkSingleBlack (20, 0) 13428 .north (-3, 13) (-21, -25) = true := by
  decide +kernel

end LangtonsAnt
