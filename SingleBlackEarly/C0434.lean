import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0434 : checkSingleBlack (17, 5) 13101 .west (-6, 2) (-26, -3) = true := by
  decide +kernel

end LangtonsAnt
