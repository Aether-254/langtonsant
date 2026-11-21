import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0933 : checkSingleBlackFast (-14, 12) 8289 .east (2, -5) (-19, -21) = true := by
  decide +kernel

end LangtonsAnt
