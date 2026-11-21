import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1394 : checkSingleBlack (-16, 2) 14568 .south (-3, -5) (-19, -21) = true := by
  decide +kernel

end LangtonsAnt
