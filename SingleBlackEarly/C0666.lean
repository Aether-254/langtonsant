import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0666 : checkSingleBlackFast (12, -9) 8351 .west (-8, 1) (-18, -18) = true := by
  decide +kernel

end LangtonsAnt
