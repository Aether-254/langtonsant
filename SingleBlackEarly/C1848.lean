import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1848 : checkSingleBlack (-60, -36) 14411 .west (17, 27) (-46, 7) = true := by
  decide +kernel

end LangtonsAnt
