import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2190 : checkSingleBlack (-91, -65) 14076 .north (34, 26) (-60, -42) = true := by
  decide +kernel

end LangtonsAnt
