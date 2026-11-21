import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1649 : checkSingleBlackFast (-42, -19) 13431 .west (8, 18) (-37, -2) = true := by
  decide +kernel

end LangtonsAnt
