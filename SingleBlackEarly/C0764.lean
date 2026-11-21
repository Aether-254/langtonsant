import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0764 : checkSingleBlack (20, -15) 14084 .north (-2, 2) (-26, 4) = true := by
  decide +kernel

end LangtonsAnt
