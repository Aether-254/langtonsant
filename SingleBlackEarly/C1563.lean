import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1563 : checkSingleBlackFast (-34, -12) 14931 .east (8, 2) (-5, -28) = true := by
  decide +kernel

end LangtonsAnt
