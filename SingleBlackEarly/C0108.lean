import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0108 : checkSingleBlackFast (-6, 3) 19791 .west (-1, 16) (-29, -19) = true := by
  decide +kernel

end LangtonsAnt
