import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0081 : checkSingleBlackFast (5, -3) 7385 .east (-2, -10) (-18, -13) = true := by
  decide +kernel

end LangtonsAnt
