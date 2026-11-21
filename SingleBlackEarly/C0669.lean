import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0669 : checkSingleBlackFast (15, -9) 9848 .north (1, -4) (-23, -2) = true := by
  decide +kernel

end LangtonsAnt
