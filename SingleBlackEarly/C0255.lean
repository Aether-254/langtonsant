import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0255 : checkSingleBlackFast (12, 10) 3095 .east (-4, -5) (-8, -12) = true := by
  decide +kernel

end LangtonsAnt
