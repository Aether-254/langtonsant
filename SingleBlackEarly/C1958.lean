import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1958 : checkSingleBlack (-70, -46) 14931 .west (22, 32) (-51, 12) = true := by
  decide +kernel

end LangtonsAnt
