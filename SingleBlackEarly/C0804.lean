import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0804 : checkSingleBlackFast (23, -4) 9896 .north (1, -2) (-23, 0) = true := by
  decide +kernel

end LangtonsAnt
