import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1631 : checkSingleBlackFast (-41, -17) 13431 .west (7, 18) (-37, -1) = true := by
  decide +kernel

end LangtonsAnt
