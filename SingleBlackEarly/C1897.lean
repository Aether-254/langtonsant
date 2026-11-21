import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1897 : checkSingleBlack (-63, -43) 45578 .north (43, 26) (-70, -9) = true := by
  decide +kernel

end LangtonsAnt
