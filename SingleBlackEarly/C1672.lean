import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1672 : checkSingleBlack (-44, -20) 13579 .west (9, 19) (-38, -1) = true := by
  decide +kernel

end LangtonsAnt
