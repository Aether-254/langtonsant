import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2073 : checkSingleBlack (-79, -59) 46410 .north (51, 34) (-78, -17) = true := by
  decide +kernel

end LangtonsAnt
