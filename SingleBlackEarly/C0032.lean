import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0032 : checkSingleBlackFast (0, 4) 4360 .south (-5, -5) (-15, -7) = true := by
  decide +kernel

end LangtonsAnt
