import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1686 : checkSingleBlackFast2 (-46, -18) 16369 .west (16, 22) (-42, -1) = true := by
  decide +kernel

end LangtonsAnt
