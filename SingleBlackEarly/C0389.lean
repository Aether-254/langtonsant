import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0389 : checkSingleBlackFast (13, 3) 5519 .west (-5, -1) (-18, -3) = true := by
  decide +kernel

end LangtonsAnt
