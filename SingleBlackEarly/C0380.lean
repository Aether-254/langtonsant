import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0380 : checkSingleBlackFast (16, -2) 7881 .west (-5, -2) (-14, -18) = true := by
  decide +kernel

end LangtonsAnt
