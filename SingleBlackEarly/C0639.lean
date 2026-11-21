import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0639 : checkSingleBlackFast (11, -9) 10123 .west (-8, 0) (-19, -18) = true := by
  decide +kernel

end LangtonsAnt
