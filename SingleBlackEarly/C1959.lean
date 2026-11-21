import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1959 : checkSingleBlackFast (-70, -48) 19443 .east (25, 19) (-8, -37) = true := by
  decide +kernel

end LangtonsAnt
