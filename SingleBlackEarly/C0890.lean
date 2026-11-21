import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0890 : checkSingleBlack (-9, -4) 13472 .south (-13, 1) (-27, -7) = true := by
  decide +kernel

end LangtonsAnt
