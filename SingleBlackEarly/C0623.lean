import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0623 : checkSingleBlackFast (7, -8) 11148 .north (1, -2) (-25, -2) = true := by
  decide +kernel

end LangtonsAnt
