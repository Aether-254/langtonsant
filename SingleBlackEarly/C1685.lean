import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1685 : checkSingleBlackFast (-46, -19) 11784 .north (11, 3) (-37, -19) = true := by
  decide +kernel

end LangtonsAnt
