import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1904 : checkSingleBlack (-65, -39) 12724 .north (21, 13) (-47, -29) = true := by
  decide +kernel

end LangtonsAnt
