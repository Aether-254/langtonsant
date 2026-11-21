import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0212 : checkSingleBlack (7, 7) 106593 .west (11, -5) (-63, -16) = true := by
  decide +kernel

end LangtonsAnt
