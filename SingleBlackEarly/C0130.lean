import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0130 : checkSingleBlackFast (5, 0) 23022 .south (-11, 2) (-38, -5) = true := by
  decide +kernel

end LangtonsAnt
