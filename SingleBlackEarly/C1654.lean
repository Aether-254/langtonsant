import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1654 : checkSingleBlack (-41, -20) 13818 .north (14, 2) (-41, -13) = true := by
  decide +kernel

end LangtonsAnt
