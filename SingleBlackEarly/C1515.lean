import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1515 : checkSingleBlack (-30, -5) 18622 .north (1, -6) (-34, -13) = true := by
  decide +kernel

end LangtonsAnt
