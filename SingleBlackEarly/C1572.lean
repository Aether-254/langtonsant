import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1572 : checkSingleBlackFast (-32, -12) 28805 .west (3, 3) (-35, -16) = true := by
  decide +kernel

end LangtonsAnt
