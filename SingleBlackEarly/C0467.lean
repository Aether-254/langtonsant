import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0467 : checkSingleBlackFast (17, 14) 4968 .north (1, -5) (-17, -9) = true := by
  decide +kernel

end LangtonsAnt
