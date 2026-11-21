import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0547 : checkSingleBlackFast (9, -5) 9700 .south (-5, -3) (-23, -15) = true := by
  decide +kernel

end LangtonsAnt
