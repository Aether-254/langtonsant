import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1609 : checkSingleBlackFast (-39, -15) 13327 .west (6, 17) (-36, -2) = true := by
  decide +kernel

end LangtonsAnt
