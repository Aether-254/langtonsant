import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1543 : checkSingleBlackFast (-33, -9) 13015 .west (3, 14) (-33, -5) = true := by
  decide +kernel

end LangtonsAnt
