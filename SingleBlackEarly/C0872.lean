import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0872 : checkSingleBlack (-6, -1) 14644 .north (-1, 9) (-5, -29) = true := by
  decide +kernel

end LangtonsAnt
