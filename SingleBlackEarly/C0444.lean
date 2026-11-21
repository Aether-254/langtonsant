import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0444 : checkSingleBlackFast (17, 7) 6336 .south (-12, -1) (-20, -7) = true := by
  decide +kernel

end LangtonsAnt
