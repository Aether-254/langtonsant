import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2042 : checkSingleBlackFast (-77, -52) 21791 .east (41, 20) (-5, -59) = true := by
  decide +kernel

end LangtonsAnt
