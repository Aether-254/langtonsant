import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0004 : checkSingleBlackFast2 (-1, 0) 12551 .west (-3, 13) (-30, -5) = true := by
  decide +kernel

end LangtonsAnt
