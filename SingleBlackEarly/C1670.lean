import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1670 : checkSingleBlack (-43, -21) 14961 .west (9, 18) (-38, -2) = true := by
  decide +kernel

end LangtonsAnt
