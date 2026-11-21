import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0278 : checkSingleBlackFast (16, 8) 81109 .east (-3, -18) (-46, -20) = true := by
  decide +kernel

end LangtonsAnt
