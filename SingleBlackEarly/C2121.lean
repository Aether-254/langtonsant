import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2121 : checkSingleBlack (-83, -64) 77001 .east (45, 26) (-76, 10) = true := by
  decide +kernel

end LangtonsAnt
