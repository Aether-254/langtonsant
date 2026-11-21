import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0512 : checkSingleBlackFast2 (-5, -5) 11890 .south (-13, 4) (-26, -1) = true := by
  decide +kernel

end LangtonsAnt
