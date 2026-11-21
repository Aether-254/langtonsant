import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2212 : checkSingleBlack (-93, -67) 14180 .north (35, 27) (-61, -43) = true := by
  decide +kernel

end LangtonsAnt
