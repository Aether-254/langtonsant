import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0835 : checkSingleBlackFast (20, 3) 14094 .south (-18, -4) (-31, -3) = true := by
  decide +kernel

end LangtonsAnt
