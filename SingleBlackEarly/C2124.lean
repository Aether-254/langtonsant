import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2124 : checkSingleBlack (-85, -59) 13764 .north (31, 23) (-57, -39) = true := by
  decide +kernel

end LangtonsAnt
