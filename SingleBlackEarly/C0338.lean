import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0338 : checkSingleBlackFast (2, 12) 19261 .west (-5, 11) (-31, -22) = true := by
  decide +kernel

end LangtonsAnt
