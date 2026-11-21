import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0321 : checkSingleBlackFast (-1, 11) 9037 .west (-6, -6) (-26, -1) = true := by
  decide +kernel

end LangtonsAnt
