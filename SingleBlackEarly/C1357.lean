import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1357 : checkSingleBlackFast (-15, 5) 11604 .north (2, -2) (-28, 6) = true := by
  decide +kernel

end LangtonsAnt
