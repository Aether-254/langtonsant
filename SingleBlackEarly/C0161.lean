import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0161 : checkSingleBlackFast (0, 9) 2686 .north (5, -4) (-14, -7) = true := by
  decide +kernel

end LangtonsAnt
