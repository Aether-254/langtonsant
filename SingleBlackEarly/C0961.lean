import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0961 : checkSingleBlackFast (5, 19) 12136 .south (-5, -18) (-9, -28) = true := by
  decide +kernel

end LangtonsAnt
