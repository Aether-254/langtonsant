import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0356 : checkSingleBlackFast (12, -1) 30535 .east (-14, -7) (-34, -8) = true := by
  decide +kernel

end LangtonsAnt
