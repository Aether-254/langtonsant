import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1561 : checkSingleBlackFast (-34, -11) 13015 .west (4, 14) (-33, -6) = true := by
  decide +kernel

end LangtonsAnt
