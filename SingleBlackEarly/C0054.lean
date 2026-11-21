import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0054 : checkSingleBlackFast (3, -1) 1304 .south (-5, -6) (-11, -6) = true := by
  decide +kernel

end LangtonsAnt
