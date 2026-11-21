import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1044 : checkSingleBlack (-12, -2) 13130 .north (3, -2) (-26, -15) = true := by
  decide +kernel

end LangtonsAnt
