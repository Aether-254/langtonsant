import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0401 : checkSingleBlackFast (12, -7) 5686 .north (-5, 11) (-14, -18) = true := by
  decide +kernel

end LangtonsAnt
