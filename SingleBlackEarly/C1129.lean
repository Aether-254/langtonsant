import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1129 : checkSingleBlackFast (26, -18) 11369 .west (-16, 5) (-23, -25) = true := by
  decide +kernel

end LangtonsAnt
