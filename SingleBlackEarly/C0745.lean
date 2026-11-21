import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0745 : checkSingleBlackFast (20, -13) 24543 .east (-11, -4) (-31, -25) = true := by
  decide +kernel

end LangtonsAnt
