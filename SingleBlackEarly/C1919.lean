import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1919 : checkSingleBlack (-65, -45) 45682 .north (44, 27) (-71, -10) = true := by
  decide +kernel

end LangtonsAnt
