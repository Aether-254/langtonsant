import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0192 : checkSingleBlackFast (9, 0) 2980 .north (2, 4) (-14, -8) = true := by
  decide +kernel

end LangtonsAnt
