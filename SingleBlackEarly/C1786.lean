import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1786 : checkSingleBlack (-53, -32) 14442 .north (20, 8) (-47, -19) = true := by
  decide +kernel

end LangtonsAnt
