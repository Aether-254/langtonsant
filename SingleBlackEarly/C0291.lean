import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0291 : checkSingleBlackFast (13, 11) 4212 .north (0, -4) (-20, -6) = true := by
  decide +kernel

end LangtonsAnt
