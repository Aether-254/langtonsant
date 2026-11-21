import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0820 : checkSingleBlack (24, -1) 13711 .east (-6, 4) (-25, -22) = true := by
  decide +kernel

end LangtonsAnt
