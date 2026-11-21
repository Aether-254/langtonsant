import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1661 : checkSingleBlackFast (-39, -21) 11488 .north (9, 1) (-35, -17) = true := by
  decide +kernel

end LangtonsAnt
