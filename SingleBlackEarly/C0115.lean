import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0115 : checkSingleBlackFast (5, 5) 3417 .west (-3, 2) (-16, -8) = true := by
  decide +kernel

end LangtonsAnt
