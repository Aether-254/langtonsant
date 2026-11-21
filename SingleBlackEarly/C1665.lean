import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1665 : checkSingleBlackFast (-44, -18) 11796 .north (11, 3) (-37, -19) = true := by
  decide +kernel

end LangtonsAnt
