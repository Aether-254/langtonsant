import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0281 : checkSingleBlackFast (15, 10) 8438 .south (-13, -10) (-20, -11) = true := by
  decide +kernel

end LangtonsAnt
