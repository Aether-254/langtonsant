import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0354 : checkSingleBlackFast (-1, 6) 23490 .south (-26, -12) (-13, -27) = true := by
  decide +kernel

end LangtonsAnt
