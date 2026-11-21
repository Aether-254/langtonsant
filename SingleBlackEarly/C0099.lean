import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0099 : checkSingleBlackFast (-3, 5) 1588 .north (5, 4) (-9, -6) = true := by
  decide +kernel

end LangtonsAnt
