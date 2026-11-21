import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0824 : checkSingleBlack (21, -2) 13771 .east (-6, 4) (-25, -22) = true := by
  decide +kernel

end LangtonsAnt
