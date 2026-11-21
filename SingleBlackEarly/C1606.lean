import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1606 : checkSingleBlack (-38, -14) 13267 .west (6, 16) (-35, -4) = true := by
  decide +kernel

end LangtonsAnt
