import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0686 : checkSingleBlack (19, -10) 13215 .east (-9, 1) (-22, -25) = true := by
  decide +kernel

end LangtonsAnt
