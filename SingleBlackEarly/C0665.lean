import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0665 : checkSingleBlackFast (14, -10) 8339 .west (-8, 1) (-18, -18) = true := by
  decide +kernel

end LangtonsAnt
