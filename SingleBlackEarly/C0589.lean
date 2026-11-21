import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0589 : checkSingleBlackFast (19, 6) 12980 .north (-5, 6) (-3, -26) = true := by
  decide +kernel

end LangtonsAnt
