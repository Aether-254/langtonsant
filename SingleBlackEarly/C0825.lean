import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0825 : checkSingleBlack (22, -1) 46998 .north (-9, -8) (-38, -23) = true := by
  decide +kernel

end LangtonsAnt
