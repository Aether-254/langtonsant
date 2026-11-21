import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1675 : checkSingleBlackFast (-45, -21) 13639 .west (9, 20) (-39, 1) = true := by
  decide +kernel

end LangtonsAnt
