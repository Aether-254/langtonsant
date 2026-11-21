import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0638 : checkSingleBlackFast (11, -8) 9147 .west (-8, 1) (-18, -18) = true := by
  decide +kernel

end LangtonsAnt
