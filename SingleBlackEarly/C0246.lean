import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0246 : checkSingleBlackFast (12, 5) 7016 .south (-8, -6) (-20, -12) = true := by
  decide +kernel

end LangtonsAnt
