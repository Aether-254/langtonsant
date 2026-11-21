import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2205 : checkSingleBlack (-91, -71) 47034 .north (57, 40) (-84, -23) = true := by
  decide +kernel

end LangtonsAnt
