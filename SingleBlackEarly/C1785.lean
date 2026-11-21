import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1785 : checkSingleBlackFast (-55, -31) 14159 .west (14, 25) (-44, 6) = true := by
  decide +kernel

end LangtonsAnt
