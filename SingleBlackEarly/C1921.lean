import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1921 : checkSingleBlackFast (-64, -45) 21128 .north (34, 30) (-60, -22) = true := by
  decide +kernel

end LangtonsAnt
