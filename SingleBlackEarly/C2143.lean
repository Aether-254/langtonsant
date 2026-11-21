import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2143 : checkSingleBlack (-85, -66) 77209 .east (46, 27) (-77, 11) = true := by
  decide +kernel

end LangtonsAnt
