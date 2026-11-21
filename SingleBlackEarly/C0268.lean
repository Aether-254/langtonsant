import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0268 : checkSingleBlack (14, 7) 14076 .south (-12, -3) (-20, -23) = true := by
  decide +kernel

end LangtonsAnt
