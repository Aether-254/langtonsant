import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0322 : checkSingleBlackFast (-2, 11) 5235 .east (-2, -8) (-15, -12) = true := by
  decide +kernel

end LangtonsAnt
