import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0106 : checkSingleBlackFast (-5, 5) 3832 .south (-3, 2) (-19, -2) = true := by
  decide +kernel

end LangtonsAnt
