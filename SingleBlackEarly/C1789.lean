import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1789 : checkSingleBlackFast (-52, -33) 20504 .north (28, 24) (-54, -16) = true := by
  decide +kernel

end LangtonsAnt
