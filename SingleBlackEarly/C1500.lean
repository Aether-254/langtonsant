import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1500 : checkSingleBlack (-27, -6) 46366 .north (7, 9) (-28, -32) = true := by
  decide +kernel

end LangtonsAnt
